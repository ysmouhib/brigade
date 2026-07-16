"""Tests for the v2 proving-power upgrades: tactic cascade, sampled first attempts,
REPL env caching + goal extraction, premise retrieval, prover-model routing, and
SQLite persistence. Acceptance semantics must be unchanged throughout: VERIFIED still
means Lean compiled the exact pinned theorem with no errors and no sorries."""
import asyncio
import json

import httpx
import pytest

from app import retrieval
from app.lean.verifier import FakeLean, ReplLeanVerifier, VerifyResult
from app.llm import RoutedLLM, ScriptedLLM
from app.models import Job, JobStatus, NodeStatus
from app.orchestrator import CASCADE_BODY, Orchestrator
from app.store import Store
from app.testing import demo_config


def _handler(lemma_bodies, forbid=()):
    """Minimal scripted brigade: one planned lemma + root."""
    def handler(role, user, n):
        if role == "skeptic":
            return json.dumps({"is_checkable": False, "claim_expr": "", "candidates": []})
        if role == "brainstormer":
            return json.dumps({"strategy_name": "s", "key_ideas": [], "proof_sketch": "p",
                               "candidate_lemmas": [], "risks": "", "confidence": 0.5})
        if role == "strategist":
            return json.dumps({"chosen_strategy": "s", "main_theorem_informal": "main claim",
                               "lemmas": [{"informal": "helper fact", "sketch": ""}],
                               "assembly_note": "combine"})
        if role == "formalizer":
            name = user.split("TARGET lean_name: ")[1].split("\n")[0]
            return json.dumps({"lean_statement": f"theorem {name} : True",
                               "faithfulness_note": "d"})
        if role == "prover":
            name = user.split("TARGET lean_name: ")[1].split("\n")[0]
            assert name not in forbid, f"prover must not be consulted for {name}"
            bodies = lemma_bodies[name]
            body = bodies[min(n, len(bodies) - 1)] if isinstance(bodies, list) else bodies
            return json.dumps({"proof": body, "claims_false": False, "why": ""})
        if role == "critic":
            return json.dumps({"diagnosis": "d", "fix_hint": "", "suggest_decompose": False})
        if role == "chef":
            return json.dumps({"summary": "s", "instructions": "i", "report": "r"})
        return json.dumps({})
    return handler


# --------------------------------------------------------------------- tactic cascade
async def test_cascade_proves_lemma_with_zero_prover_calls():
    """A lemma the automation closes must never reach an LLM prover (forbid asserts it)."""
    lean = FakeLean(rules={"lemma_1": (["omega"], "error: unsolved goals"),
                           "thm_main": (["lemma_1"], "error: unsolved goals")})
    cfg = demo_config(max_rounds=1, verify_policy="full", tactic_cascade=True)
    job = Job(problem="Prove the main claim.")
    orch = Orchestrator(job, ScriptedLLM(_handler({"thm_main": "exact lemma_1"},
                                                  forbid={"lemma_1"})), lean, cfg)
    await orch.run()
    assert job.status == JobStatus.PROVED
    lemma = next(n for n in job.nodes.values() if n.lean_name == "lemma_1")
    assert lemma.status == NodeStatus.VERIFIED and lemma.lean_proof == CASCADE_BODY
    assert any(e.type == "verified" and "cascade" in e.content for e in job.events)
    # I1 stays intact: the cascade proof text (as indented into the theorem) was
    # seen and OK'd by the verifier
    import textwrap
    indented = textwrap.indent(CASCADE_BODY, "  ")
    assert any(indented in code and "lemma_1" in code for code in lean.calls)


async def test_cascade_failure_falls_through_to_provers():
    lean = FakeLean(rules={"lemma_1": (["alpha"], "error: unsolved goals"),
                           "thm_main": (["lemma_1"], "error: unsolved goals")})
    cfg = demo_config(max_rounds=1, verify_policy="full", tactic_cascade=True)
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, ScriptedLLM(_handler({"lemma_1": "alpha",
                                                  "thm_main": "exact lemma_1"})), lean, cfg).run()
    assert job.status == JobStatus.PROVED
    lemma = next(n for n in job.nodes.values() if n.lean_name == "lemma_1")
    assert lemma.lean_proof == "alpha"   # the LLM proof, not the cascade


# ------------------------------------------------------------------ sampled attempts
async def test_sampled_first_attempt_finds_the_one_passing_candidate():
    lean = FakeLean(rules={"lemma_1": (["gamma"], "error: unsolved goals"),
                           "thm_main": (["lemma_1"], "error: unsolved goals")})
    cfg = demo_config(max_rounds=1, verify_policy="full", prove_samples=3)
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, ScriptedLLM(_handler(
        {"lemma_1": ["alpha", "beta", "gamma"], "thm_main": "exact lemma_1"})), lean, cfg).run()
    assert job.status == JobStatus.PROVED
    lemma = next(n for n in job.nodes.values() if n.lean_name == "lemma_1")
    assert lemma.status == NodeStatus.VERIFIED and lemma.lean_proof == "gamma"
    assert lemma.attempts == 3
    assert any(e.type == "prove_attempt" and "sampled candidate" in e.content
               for e in job.events)


async def test_sampled_attempt_failure_feeds_repair_cycle():
    lean = FakeLean(rules={"lemma_1": (["delta"], "error: unsolved goals in lemma_1"),
                           "thm_main": (["lemma_1"], "error: unsolved goals")})
    cfg = demo_config(max_rounds=1, verify_policy="full", prove_samples=2)
    # both samples fail; the repair cycle (call #2 per role/target counter) succeeds
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, ScriptedLLM(_handler(
        {"lemma_1": ["alpha", "beta", "delta"], "thm_main": "exact lemma_1"})), lean, cfg).run()
    assert job.status == JobStatus.PROVED
    lemma = next(n for n in job.nodes.values() if n.lean_name == "lemma_1")
    assert lemma.lean_proof == "delta"


# ------------------------------------------------------- REPL env cache + goal states
class _StubRepl(ReplLeanVerifier):
    def __init__(self):
        super().__init__(project_dir=".", repl_bin="repl")
        self.sent: list[dict] = []
        self._base_env = 0

    async def _ensure_started(self):
        class _P:  # looks alive
            returncode = None
        self._proc = _P()

    async def _roundtrip(self, obj, timeout):
        self.sent.append(obj)
        if obj["cmd"].startswith("theorem good_stmt") and "sorry" in obj["cmd"]:
            return {"env": 7, "sorries": [{"goal": "⊢ Even (n * (n + 1))"}], "messages": []}
        if obj.get("env") == 0 and obj["cmd"].startswith("theorem helper"):
            return {"env": 5, "messages": []}          # context elaboration
        return {"env": 9, "messages": [], "sorries": []}


async def test_repl_caches_context_env_and_extracts_goals():
    v = _StubRepl()
    ctx = "theorem helper : True := by\n  trivial"
    r1 = await v.check("theorem a : True := by trivial", context=ctx)
    r2 = await v.check("theorem b : True := by trivial", context=ctx)
    assert r1.ok and r2.ok
    ctx_sends = [o for o in v.sent if o["cmd"] == ctx]
    assert len(ctx_sends) == 1, "context must be elaborated once, then reused via env id"
    assert all(o.get("env") == 5 for o in v.sent if o["cmd"].startswith("theorem a")
               or o["cmd"].startswith("theorem b"))
    g = await v.check("theorem good_stmt (n : ℕ) : Even (n * (n + 1)) := by\n  sorry")
    assert g.sorries == 1 and g.goals == ["⊢ Even (n * (n + 1))"]


# ----------------------------------------------------------------- premise retrieval
async def test_retrieval_loogle_parses_hits_and_swallows_failures():
    def ok(request):
        assert request.url.host == "loogle.lean-lang.org"
        return httpx.Response(200, json={"hits": [
            {"name": "Nat.even_mul_succ_self", "type": "∀ (n : ℕ), Even (n * (n + 1))"},
            {"name": "Even.add", "type": "Even a → Even b → Even (a + b)"}]})
    client = httpx.AsyncClient(transport=httpx.MockTransport(ok))
    hits = await retrieval.search("loogle", "Even (n * (n + 1))", client=client)
    assert hits[0].startswith("Nat.even_mul_succ_self : ")
    await client.aclose()

    def boom(request):
        return httpx.Response(500)
    client = httpx.AsyncClient(transport=httpx.MockTransport(boom))
    assert await retrieval.search("loogle", "anything", client=client) == []
    await client.aclose()
    assert await retrieval.search("off", "anything") == []


# ------------------------------------------------------------------- prover routing
async def test_routed_llm_sends_prover_role_to_the_dedicated_model():
    calls = []

    class _Tag:
        def __init__(self, tag): self.tag = tag
        async def complete(self, *, role, system, user, temperature=0.3,
                           max_tokens=2000, model=None):
            calls.append((self.tag, role))
            return "{}"

    llm = RoutedLLM(_Tag("primary"), _Tag("prover"))
    await llm.complete(role="strategist", system="", user="")
    await llm.complete(role="prover", system="", user="")
    assert calls == [("primary", "strategist"), ("prover", "prover")]


# --------------------------------------------------------------------- persistence
async def test_sqlite_store_survives_restart(tmp_path):
    db = str(tmp_path / "jobs.db")
    store = Store(db)
    job = Job(problem="persist me")
    job.status = JobStatus.PROVED

    async def _noop():
        pass
    task = asyncio.get_event_loop().create_task(_noop())
    store.add(job, task)
    await task
    await asyncio.sleep(0)      # let the done-callback fire
    store.persist(job.id)
    await store.shutdown()

    reborn = Store(db)
    loaded = reborn.get(job.id)
    assert loaded is not None and loaded.problem == "persist me"
    assert loaded.status == JobStatus.PROVED
    await reborn.shutdown()
