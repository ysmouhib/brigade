"""Tests for VERIFY_POLICY=strategic: probe lemmas numerically, batch sibling proof checks.

Soundness must be identical to 'full': VERIFIED still means Lean compiled the theorem with
no errors and no sorries — strategic only changes how many theorems share one Lean call.
"""
import json

from app.lean.verifier import FakeLean
from app.llm import ScriptedLLM
from app.models import Job, JobStatus, NodeStatus
from app.orchestrator import Orchestrator
from app.testing import demo_config


def _base_handler(lemma_bodies, skeptic_lemma=None):
    """Minimal scripted brigade: 2 planned lemmas + root, first-try proofs."""
    def handler(role, user, n):
        if role == "skeptic":
            if skeptic_lemma and skeptic_lemma["match"] in user:
                return json.dumps(skeptic_lemma["reply"])
            return json.dumps({"is_checkable": False, "claim_expr": "", "candidates": []})
        if role == "brainstormer":
            return json.dumps({"strategy_name": "s", "key_ideas": [], "proof_sketch": "p",
                               "candidate_lemmas": [], "risks": "", "confidence": 0.5})
        if role == "strategist":
            return json.dumps({"chosen_strategy": "s", "main_theorem_informal": "main claim",
                               "lemmas": [{"informal": "first helper fact", "sketch": ""},
                                          {"informal": "every prime is odd", "sketch": ""}],
                               "assembly_note": "combine"})
        if role == "formalizer":
            name = user.split("TARGET lean_name: ")[1].split("\n")[0]
            return json.dumps({"lean_statement": f"theorem {name} : True",
                               "faithfulness_note": "d"})
        if role == "prover":
            name = user.split("TARGET lean_name: ")[1].split("\n")[0]
            body = lemma_bodies.get(name)
            if body is None:
                raise AssertionError(f"prover must not be consulted for {name}")
            return json.dumps({"proof": body, "claims_false": False, "why": ""})
        if role == "critic":
            return json.dumps({"diagnosis": "d", "fix_hint": "", "suggest_decompose": False})
        if role == "chef":
            return json.dumps({"summary": "s", "instructions": "i", "report": "r"})
        return json.dumps({})
    return handler


async def test_strategic_batches_sibling_first_attempts():
    lean = FakeLean(rules={"lemma_1": (["alpha"], "error: unsolved goals"),
                           "lemma_2": (["beta"], "error: unsolved goals"),
                           "thm_main": (["lemma_1", "lemma_2"], "error: unsolved goals")})
    handler = _base_handler({"lemma_1": "alpha", "lemma_2": "beta",
                             "thm_main": "exact lemma_1.trans lemma_2"})
    cfg = demo_config(max_rounds=1)
    cfg.verify_policy = "strategic"
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, ScriptedLLM(handler), lean, cfg).run()

    assert job.status == JobStatus.PROVED
    # exactly ONE Lean call carries both lemma proofs (the batch), none carries just one
    both = [c for c in lean.calls
            if "alpha" in c and "beta" in c and "sorry" not in c and "thm_main" not in c]
    solo = [c for c in lean.calls if ("alpha" in c) ^ ("beta" in c) and "sorry" not in c]
    assert len(both) == 1 and not solo
    # 3 statement gates + 1 batched lemmas + 1 root + 1 final assembly = 6 Lean calls
    assert len(lean.calls) == 6
    assert sum(1 for e in job.events if e.type == "verified" and "batched" in e.content) == 2
    # soundness: every verified node's exact theorem text appeared in an OK Lean call
    for node in job.nodes.values():
        assert node.status == NodeStatus.VERIFIED
        thm = f"{node.lean_statement} := by"
        assert any(thm in c and "sorry" not in c for c in lean.calls)


async def test_strategic_batch_failure_falls_back_to_individual_checks():
    lean = FakeLean(rules={"lemma_1": (["alpha"], "error: unsolved goals"),
                           "lemma_2": (["beta"], "error: unsolved goals"),
                           "thm_main": (["lemma_1"], "error: unsolved goals")})
    # lemma_2's first body is wrong -> combined check fails -> individual split:
    # lemma_1 verifies, lemma_2 enters the normal repair cycle and succeeds on retry
    bodies = {"lemma_1": ["alpha"], "lemma_2": ["wrong", "beta"], "thm_main": ["use lemma_1"]}
    counts = {}

    def handler(role, user, n):
        if role == "prover":
            name = user.split("TARGET lean_name: ")[1].split("\n")[0]
            i = counts.get(name, 0); counts[name] = i + 1
            opts = bodies[name]
            return json.dumps({"proof": opts[min(i, len(opts) - 1)],
                               "claims_false": False, "why": ""})
        return _base_handler({})(role, user, n)

    cfg = demo_config(max_rounds=1)
    cfg.verify_policy = "strategic"
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, ScriptedLLM(handler), lean, cfg).run()

    assert job.status == JobStatus.PROVED
    assert any(e.type == "batch_split" for e in job.events)
    lemma2 = next(n for n in job.nodes.values() if n.lean_name == "lemma_2")
    assert lemma2.status == NodeStatus.VERIFIED and lemma2.attempts == 2


async def test_strategic_probe_refutes_false_lemma_before_any_proving():
    skeptic_lemma = {
        "match": "every prime is odd",
        "reply": {"is_checkable": True,
                  "claim_expr": "Or(Not(isprime({n})), Eq(Mod({n}, 2), 1))",
                  "candidates": [{"n": k} for k in range(1, 8)],
                  "notes": "false at 2"},
    }
    # provers must never run: passing an empty body map makes any prover call raise
    handler = _base_handler({}, skeptic_lemma=skeptic_lemma)
    cfg = demo_config(max_rounds=1)
    cfg.verify_policy = "strategic"
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, ScriptedLLM(handler), FakeLean(), cfg).run()

    assert job.status == JobStatus.EXHAUSTED           # plan died, budgets honored
    bad = next(n for n in job.nodes.values() if n.informal == "every prime is odd")
    assert bad.status == NodeStatus.REFUTED
    assert any(e.type == "lemma_refuted" and e.node_id == bad.id for e in job.events)
    assert not any(e.agent == "prover" for e in job.events)
    assert job.refutation is None                       # the MAIN claim was not refuted
    # the chef's next-round feedback names the refuted lemma
    retro_or_exhaust = [e for e in job.events if e.type in ("retrospective", "exhausted")]
    assert retro_or_exhaust
