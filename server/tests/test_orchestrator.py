"""End-to-end orchestrator tests against the deterministic demo scenario.

The scenario (app/testing.py) forces every mechanism to fire; these tests assert both
the happy path AND the safety invariants (nothing is VERIFIED unless the verifier said OK).
"""
import json

import pytest

from app.llm import ScriptedLLM
from app.models import Job, JobStatus, NodeStatus
from app.orchestrator import Orchestrator
from app.testing import DEMO_PROBLEM, default_fake_lean, demo_config, demo_llm


async def run_demo():
    job = Job(problem=DEMO_PROBLEM)
    lean = default_fake_lean()
    orch = Orchestrator(job, demo_llm(), lean, demo_config())
    await orch.run()
    return job, lean


@pytest.fixture(scope="module")
def demo_result():
    import asyncio
    return asyncio.run(run_demo())


def test_job_is_proved(demo_result):
    job, _ = demo_result
    assert job.status == JobStatus.PROVED
    assert job.final_lean and "sorry" not in job.final_lean
    for name in ("thm_main", "lemma_1", "lemma_2", "lemma_2_a", "lemma_2_b"):
        assert name in job.final_lean


def test_full_hierarchy_participated(demo_result):
    job, _ = demo_result
    levels = {e.level for e in job.events}
    assert {"chef", "sous", "worker", "lean"} <= levels
    agents_seen = {e.agent for e in job.events}
    assert any(a.startswith("brainstormer") for a in agents_seen)
    assert {"skeptic", "strategist", "formalizer", "prover", "critic",
            "lean_verifier", "chef"} <= agents_seen
    # three brainstormers ran in parallel in round 1
    assert sum(1 for e in job.events if e.type == "strategy") >= 3


def test_statement_gate_caught_bad_formalization(demo_result):
    job, _ = demo_result
    lemma1 = next(n for n in job.nodes.values() if n.lean_name == "lemma_1")
    attempts = [e for e in job.events
                if e.type == "statement_attempt" and e.node_id == lemma1.id]
    assert len(attempts) >= 2, "broken 'Evenn' statement should force a retry"
    assert any("Evenn" in e.content for e in job.events if e.type == "lean_check")
    assert any(e.type == "statement_ok" and e.node_id == lemma1.id for e in job.events)
    assert "Evenn" not in lemma1.lean_statement


def test_repair_cycle_happened(demo_result):
    job, _ = demo_result
    lemma1 = next(n for n in job.nodes.values() if n.lean_name == "lemma_1")
    assert lemma1.status == NodeStatus.VERIFIED
    assert lemma1.attempts >= 2, "first proof (simp) must fail before the repair succeeds"
    assert any(e.type == "triage" and e.node_id == lemma1.id for e in job.events)


def test_decomposition_escalation(demo_result):
    job, _ = demo_result
    lemma2 = next(n for n in job.nodes.values() if n.lean_name == "lemma_2")
    assert lemma2.decomposed is True
    kids = job.children(lemma2.id)
    assert sorted(k.lean_name for k in kids) == ["lemma_2_a", "lemma_2_b"]
    assert all(k.status == NodeStatus.VERIFIED for k in kids)
    assert all(k.depth == lemma2.depth + 1 for k in kids)
    assert lemma2.status == NodeStatus.VERIFIED
    assert any(e.type == "decompose" and e.node_id == lemma2.id for e in job.events)
    # the recombined proof must actually cite the sub-lemmas
    assert "lemma_2_a" in lemma2.lean_proof and "lemma_2_b" in lemma2.lean_proof


def test_invariant_no_verified_without_lean_ok(demo_result):
    """I1: every 'verified' event must be preceded by a Lean OK check on that node."""
    job, _ = demo_result
    checks_ok = {}  # node_id -> earliest seq of an OK-no-sorries lean_check
    for e in job.events:
        if e.type == "lean_check" and e.content.startswith("OK (no errors") and e.node_id:
            checks_ok.setdefault(e.node_id, e.seq)
    for e in job.events:
        if e.type == "verified":
            assert e.node_id in checks_ok and checks_ok[e.node_id] < e.seq, \
                f"node {e.node_id} marked verified without a prior Lean OK"
    verified_nodes = [n for n in job.nodes.values() if n.status == NodeStatus.VERIFIED]
    assert len(verified_nodes) == 5


def test_final_acceptance_gated_by_assembly_and_audit(demo_result):
    """I2: PROVED only after the assembled file passes a fresh check AND the axiom audit."""
    job, lean = demo_result
    proved = next(e for e in job.events if e.type == "proved")
    audit = next(e for e in job.events if e.type == "axiom_audit")
    final_checks = [e for e in job.events
                    if e.type == "lean_check" and e.node_id is None
                    and e.content.startswith("OK (no errors")]
    assert final_checks, "assembled file must be re-checked as a whole"
    assert max(0, *[c.seq for c in final_checks]) < proved.seq
    assert audit.seq < proved.seq
    assert "ok=True" in audit.content and "sorryAx" not in audit.content
    # the exact final file was seen by the verifier verbatim
    assert job.final_lean in lean.calls


def test_report_written(demo_result):
    job, _ = demo_result
    assert job.summary
    assert job.llm_calls > 0 and job.lean_calls > 0


# --------------------------------------------------------------------------- refutation
async def test_skeptic_refutes_false_claim():
    def handler(role, user, n):
        if role == "skeptic":
            return json.dumps({
                "is_checkable": True,
                "claim_expr": "Or(Not(isprime({n})), Eq(Mod({n}, 2), 1))",
                "candidates": [{"n": k} for k in range(1, 8)],
                "notes": "claims every prime is odd",
            })
        if role == "chef":
            return json.dumps({"report": "refuted by counterexample"})
        raise AssertionError(f"role {role} must never be consulted after a refutation")

    job = Job(problem="Prove that every prime number is odd.")
    orch = Orchestrator(job, ScriptedLLM(handler), default_fake_lean(), demo_config())
    await orch.run()

    assert job.status == JobStatus.REFUTED
    assert job.refutation is not None
    assert job.refutation.counterexample == {"n": 2}
    assert job.final_lean == ""
    assert not any(e.agent in ("prover", "strategist") for e in job.events)
    assert any(e.type == "refuted" for e in job.events)


# --------------------------------------------------------------------------- lint (I4)
async def test_lint_blocks_sorry_before_lean():
    """A prover that answers `sorry` must be rejected by the lint, never by Lean."""
    def handler(role, user, n):
        if role == "skeptic":
            return json.dumps({"is_checkable": False, "claim_expr": "", "candidates": []})
        if role == "brainstormer":
            return json.dumps({"strategy_name": "s", "key_ideas": ["k"], "proof_sketch": "p",
                               "candidate_lemmas": [], "risks": "", "confidence": 0.5})
        if role == "strategist":
            return json.dumps({"chosen_strategy": "s", "main_theorem_informal": "1 = 1",
                               "lemmas": [], "assembly_note": "direct"})
        if role == "formalizer":
            return json.dumps({"lean_statement": "theorem thm_main : 1 = 1",
                               "faithfulness_note": "direct"})
        if role == "prover":
            return json.dumps({"proof": "sorry", "claims_false": False, "why": ""})
        if role == "critic":
            return json.dumps({"diagnosis": "gave up", "fix_hint": "", "suggest_decompose": False})
        if role == "decomposer":
            return json.dumps({"lemmas": [], "recombine_hint": ""})
        if role == "chef":
            return json.dumps({"summary": "fail", "instructions": "retry",
                               "report": "exhausted"})
        return json.dumps({})

    job = Job(problem="Prove that 1 = 1.")
    lean = default_fake_lean()
    orch = Orchestrator(job, ScriptedLLM(handler), lean, demo_config(max_rounds=1))
    await orch.run()

    assert job.status == JobStatus.EXHAUSTED
    assert any(e.type == "lint_reject" for e in job.events)
    assert not any(n.status == NodeStatus.VERIFIED for n in job.nodes.values())
    # Lean saw `sorry` only from the intentional statement gate, never from a proof body:
    # the statement gate performs exactly one successful check per formalization attempt.
    gate_checks = sum(1 for e in job.events if e.type == "statement_attempt")
    assert sum(1 for code in lean.calls if "sorry" in code) == gate_checks


# --------------------------------------------------------------------------- pinning (I3)
def test_prover_cannot_alter_pinned_statement():
    from app.models import ProofNode
    job = Job(problem="x")
    orch = Orchestrator(job, demo_llm(), default_fake_lean(), demo_config())
    node = ProofNode(lean_name="foo", lean_statement="theorem foo (n : \u2115) : n = n")
    # prover tries to smuggle in a DIFFERENT, trivially provable statement
    echoed = "theorem foo (n : \u2115) : 1 = 1 := by\n  rfl"
    body = orch._clean_body(node, echoed)
    assert body == "rfl"
    final = orch._theorem_text(node, body)
    assert "n = n" in final and "1 = 1" not in final
    assert final.startswith("theorem foo")


def test_clean_body_strips_fences_and_by():
    job = Job(problem="x")
    orch = Orchestrator(job, demo_llm(), default_fake_lean(), demo_config())
    from app.models import ProofNode
    node = ProofNode(lean_name="foo", lean_statement="theorem foo : True")
    assert orch._clean_body(node, "```lean\nby\n  trivial\n```") == "trivial"
    assert orch._clean_body(node, "by exact trivial") == "exact trivial"
