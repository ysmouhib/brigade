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
from app.orchestrator import CASCADE_MARK, CASCADE_TACTICS, Orchestrator, cascade_body
from app.store import Store
from app.testing import demo_config


def _handler(lemma_bodies, forbid=(), n_lemmas=1, prover_calls=None):
    """Minimal scripted brigade: `n_lemmas` planned lemmas + root."""
    def handler(role, user, n):
        if role == "skeptic":
            return json.dumps({"is_checkable": False, "claim_expr": "", "candidates": []})
        if role == "brainstormer":
            return json.dumps({"strategy_name": "s", "key_ideas": [], "proof_sketch": "p",
                               "candidate_lemmas": [], "risks": "", "confidence": 0.5})
        if role == "strategist":
            return json.dumps({"chosen_strategy": "s", "main_theorem_informal": "main claim",
                               "lemmas": [{"informal": f"helper fact {i}", "sketch": ""}
                                          for i in range(n_lemmas)],
                               "assembly_note": "combine"})
        if role == "formalizer":
            name = user.split("TARGET lean_name: ")[1].split("\n")[0]
            return json.dumps({"lean_statement": f"theorem {name} : True",
                               "faithfulness_note": "d"})
        if role == "prover":
            name = user.split("TARGET lean_name: ")[1].split("\n")[0]
            assert name not in forbid, f"prover must not be consulted for {name}"
            if prover_calls is not None:
                prover_calls[name] = prover_calls.get(name, 0) + 1
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
class _CascadeLean(FakeLean):
    """FakeLean plus what real Lean prints when a cascade branch wins: the branch's
    `trace` line as an info message. `winner` lets a test claim any branch won."""

    def __init__(self, rules, winner: str, reported_for: str = "lemma_1"):
        super().__init__(rules=rules)
        self.winner, self.reported_for = winner, reported_for

    async def check(self, code, context=""):
        res = await super().check(code, context)
        if res.ok and CASCADE_MARK in code:
            res.infos = [f"{CASCADE_MARK} {self.reported_for} {self.winner}"]
        return res


def _cascade_job(lean):
    cfg = demo_config(max_rounds=1, verify_policy="full", tactic_cascade=True)
    job = Job(problem="Prove the main claim.")
    orch = Orchestrator(job, ScriptedLLM(_handler({"thm_main": "exact lemma_1"},
                                                  forbid={"lemma_1"})), lean, cfg)
    return job, orch


def test_every_cascade_branch_must_close_the_goal():
    """`ring`, `norm_num` and `simp` can succeed while leaving a rewritten goal; inside
    `first` that would stop the cascade at a branch that did not prove anything."""
    branches = [ln for ln in cascade_body("x").splitlines() if ln.strip().startswith("|")]
    assert len(branches) == len(CASCADE_TACTICS)
    for tac, ln in zip(CASCADE_TACTICS, branches):
        assert ln.strip().startswith(f"| ({tac}; done;"), ln


async def test_cascade_proves_lemma_with_zero_prover_calls_and_keeps_the_winning_tactic():
    """A lemma the automation closes never reaches an LLM prover (forbid asserts it), and
    its recorded proof is the one tactic that worked, not the whole cascade."""
    lean = _CascadeLean({"lemma_1": (["ring"], "error: unsolved goals"),
                         "thm_main": (["lemma_1"], "error: unsolved goals")}, winner="ring")
    job, orch = _cascade_job(lean)
    await orch.run()
    assert job.status == JobStatus.PROVED
    lemma = next(n for n in job.nodes.values() if n.lean_name == "lemma_1")
    assert lemma.status == NodeStatus.VERIFIED and lemma.lean_proof == "ring"
    assert any(e.type == "verified" and "cascade" in e.content and "`ring`" in e.content
               for e in job.events)
    assert "first" not in job.final_lean and CASCADE_MARK not in job.final_lean
    # I1: the exact single-tactic theorem was checked on its own before being recorded
    assert any(code.rstrip().endswith(":= by\n  ring") and "lemma_1" in code
               for code in lean.calls)


async def test_cascade_keeps_the_checked_body_when_the_single_tactic_fails():
    """If the named branch does not verify on its own, the cascade text Lean accepted
    stays (I1: never record a proof Lean has not seen)."""
    lean = _CascadeLean({"lemma_1": (["ring"], "error: unsolved goals"),
                         "thm_main": (["lemma_1"], "error: unsolved goals")}, winner="omega")
    job, orch = _cascade_job(lean)
    await orch.run()
    assert job.status == JobStatus.PROVED
    lemma = next(n for n in job.nodes.values() if n.lean_name == "lemma_1")
    assert lemma.lean_proof == cascade_body("lemma_1")


async def test_cascade_ignores_a_win_reported_for_another_lemma():
    """Context lemmas can carry their own cascade trace; only this lemma's line counts."""
    lean = _CascadeLean({"lemma_1": (["ring"], "error: unsolved goals"),
                         "thm_main": (["lemma_1"], "error: unsolved goals")},
                        winner="ring", reported_for="other_lemma")
    job, orch = _cascade_job(lean)
    await orch.run()
    lemma = next(n for n in job.nodes.values() if n.lean_name == "lemma_1")
    assert lemma.lean_proof == cascade_body("lemma_1")


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


async def test_strategic_batch_checks_a_lone_remaining_candidate():
    """Real failure from the second benchmark: the cascade closed lemma_1, which left one
    prover candidate in the strategic batch, and a batch of one was never checked. The
    (correct) first proof was dropped and the prover asked again."""
    lean = FakeLean(rules={"lemma_1": (["omega"], "error: unsolved goals"),
                           "lemma_2": (["alpha"], "error: unsolved goals"),
                           "thm_main": (["lemma_1", "lemma_2"], "error: unsolved goals")})
    calls: dict[str, int] = {}
    llm = ScriptedLLM(_handler({"lemma_2": "alpha", "thm_main": "exact ⟨lemma_1, lemma_2⟩"},
                               forbid={"lemma_1"}, n_lemmas=2, prover_calls=calls))
    cfg = demo_config(max_rounds=1, verify_policy="strategic", tactic_cascade=True,
                      quick_attempt=False)
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, llm, lean, cfg).run()
    lemma_2 = next(n for n in job.nodes.values() if n.lean_name == "lemma_2")
    assert lemma_2.status == NodeStatus.VERIFIED and lemma_2.attempts == 1
    assert calls["lemma_2"] == 1


async def test_cascade_runs_once_per_lemma():
    """The cascade does not use context lemmas, so a second try on the same statement can
    only repeat the first result. After a failed batched attempt it used to run again
    before the prover loop."""
    lean = FakeLean(rules={"lemma_1": (["omega"], "error: unsolved goals"),
                           "lemma_2": (["alpha"], "error: unsolved goals"),
                           "thm_main": (["lemma_1", "lemma_2"], "error: unsolved goals")})
    cfg = demo_config(max_rounds=1, verify_policy="strategic", tactic_cascade=True,
                      quick_attempt=False)
    job = Job(problem="Prove the main claim.")
    llm = ScriptedLLM(_handler({"lemma_2": ["beta", "alpha"], "thm_main": "exact ⟨lemma_1, lemma_2⟩"},
                               forbid={"lemma_1"}, n_lemmas=2))
    await Orchestrator(job, llm, lean, cfg).run()
    assert job.status == JobStatus.PROVED
    assert sum(1 for c in lean.calls if f"{CASCADE_MARK} lemma_2 " in c) == 1


# ------------------------------------------------------------------ quick attempt
class _Recording(ScriptedLLM):
    def __init__(self, handler):
        super().__init__(handler)
        self.roles: list[str] = []

    async def complete(self, *, role, **kw):
        self.roles.append(role)
        return await super().complete(role=role, **kw)


async def test_quick_attempt_proves_an_easy_claim_without_planning():
    """Before any brainstorm or plan, the claim is formalized as stated and Lean's own
    automation gets one try. Easy claims then cost a handful of calls, not a full plan."""
    lean = _CascadeLean({"thm_main": (["omega"], "error: unsolved goals")},
                        winner="omega", reported_for="thm_main")
    llm = _Recording(_handler({}, forbid={"thm_main"}))
    cfg = demo_config(max_rounds=1, verify_policy="full", tactic_cascade=True)
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, llm, lean, cfg).run()
    assert job.status == JobStatus.PROVED
    assert not {"brainstormer", "strategist", "prover"} & set(llm.roles)
    assert [n.lean_name for n in job.nodes.values()] == ["thm_main"]
    assert job.final_lean == "theorem thm_main : True := by\n  omega"
    assert any(e.type == "axiom_audit" for e in job.events)


async def test_quick_attempt_that_fails_leaves_no_trace_in_the_plan():
    lean = _CascadeLean({"lemma_1": (["ring"], "error: unsolved goals"),
                         "thm_main": (["lemma_1"], "error: unsolved goals")}, winner="ring")
    llm = _Recording(_handler({"thm_main": "exact lemma_1"}, forbid={"lemma_1"}))
    cfg = demo_config(max_rounds=1, verify_policy="full", tactic_cascade=True)
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, llm, lean, cfg).run()
    assert job.status == JobStatus.PROVED
    assert "brainstormer" in llm.roles                 # the full pipeline ran
    assert sorted(n.lean_name for n in job.nodes.values()) == ["lemma_1", "thm_main"]
    assert job.root().lean_name == "thm_main"
    assert any(e.type == "quick_attempt" for e in job.events)


async def test_quick_attempt_can_be_switched_off():
    lean = _CascadeLean({"thm_main": (["omega"], "error: unsolved goals")},
                        winner="omega", reported_for="thm_main")
    llm = _Recording(_handler({"lemma_1": "omega", "thm_main": "omega"}))
    cfg = demo_config(max_rounds=1, verify_policy="full", tactic_cascade=True,
                      quick_attempt=False)
    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, llm, lean, cfg).run()
    assert "brainstormer" in llm.roles


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


async def test_sampled_candidates_get_different_prompts():
    """Claude no longer accepts a temperature spread, so the k samples must differ by prompt."""
    seen: list[str] = []
    base = _handler({"lemma_1": ["alpha", "beta", "gamma"], "thm_main": "exact lemma_1"})

    def handler(role, user, n):
        if role == "prover" and "TARGET lean_name: lemma_1" in user:
            seen.append(user)
        return base(role, user, n)

    lean = FakeLean(rules={"lemma_1": (["gamma"], "error: unsolved goals"),
                           "thm_main": (["lemma_1"], "error: unsolved goals")})
    cfg = demo_config(max_rounds=1, verify_policy="full", prove_samples=3)
    await Orchestrator(Job(problem="Prove the main claim."), ScriptedLLM(handler), lean, cfg).run()
    assert len(seen) == 3 and len(set(seen)) == 3, "each sampled candidate needs its own approach"


async def test_fatal_llm_error_stops_the_job_with_a_clear_message():
    from app.llm import LLMFatalError

    class Rejecting:
        async def complete(self, **_kw):
            raise LLMFatalError("Anthropic API rejected the request (404): model not found")

    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, Rejecting(), FakeLean(), demo_config(max_rounds=2)).run()
    assert job.status == JobStatus.ERROR
    assert job.llm_calls == 1, "no budget may be burned on a request that can never succeed"
    assert "model not found" in job.events[-1].content


async def test_unreachable_api_ends_as_error_not_exhausted():
    """An outage is an infrastructure failure, not a failed proof search."""
    from app.llm import LLMUnavailableError

    class Down:
        async def complete(self, **_kw):
            raise LLMUnavailableError("Anthropic API unavailable after 3 attempts: connection refused")

    job = Job(problem="Prove the main claim.")
    await Orchestrator(job, Down(), FakeLean(), demo_config(max_rounds=2)).run()
    assert job.status == JobStatus.ERROR
    assert "unreachable" in job.events[-1].content
    assert job.llm_calls <= 4


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
