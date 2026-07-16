"""Deterministic offline scenario used by BOTH the pytest suite and `FAKE_LLM=1` demo mode.

The scenario is designed to exercise every mechanism of the hierarchy on the toy problem
"n² + n is even":

  * Skeptic probes numerically and finds no counterexample          (phase 0)
  * 3 brainstormers → Sous-Chef plans 2 lemmas                      (hierarchy levels)
  * lemma_1's FIRST formalization is broken → statement-gate repair (formalize cycle)
  * lemma_1's FIRST proof fails → Critic triage → repair succeeds   (repair cycle)
  * lemma_2 fails all repair cycles → Chef DECOMPOSES it into
    lemma_2_a / lemma_2_b, proves those, then re-proves lemma_2     (escalation)
  * root theorem proved citing both lemmas, full file re-checked,
    axiom audit passes → PROVED                                     (assembly gate)

FakeLean simulates Lean: a theorem block "compiles" iff it contains the required tokens.
That makes the verifier the ground truth even in the fake world — the LLM script cannot
mark anything proved by itself.
"""
from __future__ import annotations
import json
import re
from collections import defaultdict

from .config import Config
from .lean.verifier import FakeLean

DEMO_PROBLEM = "Prove that for every natural number n, n^2 + n is even."

NAME_RE = re.compile(r"TARGET lean_name:\s*([A-Za-z0-9_']+)")


def default_fake_lean() -> FakeLean:
    return FakeLean(
        rules={
            "lemma_1":   (["even_mul_succ_self"], "error: unsolved goals\n⊢ Even (n * (n + 1))"),
            "lemma_2":   (["lemma_2_a", "lemma_2_b"], "error: unsolved goals\n⊢ n ^ 2 + n = n * (n + 1)"),
            "lemma_2_a": (["sq"], "error: unsolved goals\n⊢ n ^ 2 = n * n"),
            "lemma_2_b": (["ring"], "error: unsolved goals\n⊢ n * n + n = n * (n + 1)"),
            "thm_main":  (["lemma_1", "lemma_2"], "error: unsolved goals\n⊢ Even (n ^ 2 + n)"),
        },
        bad_tokens={"Evenn": "error: unknown identifier 'Evenn'"},
    )


def demo_config(**overrides) -> Config:
    cfg = Config()
    cfg.fake_llm = True
    cfg.lean_mode = "fake"
    cfg.verify_policy = "full"
    cfg.max_rounds = 2
    cfg.n_brainstormers = 3
    cfg.statement_retries = 2
    cfg.repair_cycles = 2
    cfg.max_depth = 2
    cfg.tactic_cascade = False   # keep the recorded scenario byte-identical
    cfg.prove_samples = 1
    cfg.retrieval = "off"
    for k, v in overrides.items():
        setattr(cfg, k, v)
    return cfg


class DemoScript:
    """handler(role, user, global_call_index) -> JSON string, with per-(role, target) counters."""

    def __init__(self):
        self.counts: dict[tuple[str, str], int] = defaultdict(int)

    def _n(self, role: str, target: str) -> int:
        n = self.counts[(role, target)]
        self.counts[(role, target)] += 1
        return n

    def __call__(self, role: str, user: str, _gn: int) -> str:
        m = NAME_RE.search(user)
        target = m.group(1) if m else "-"
        n = self._n(role, target)
        fn = getattr(self, f"_{role}", None)
        if fn is None:
            return json.dumps({"error": f"no script for role {role}"})
        return json.dumps(fn(target, n, user), ensure_ascii=False)

    # ---- roles ----
    def _skeptic(self, t, n, user):
        return {"is_checkable": True,
                "claim_expr": "Eq(Mod({n}**2 + {n}, 2), 0)",
                "candidates": [{"n": k} for k in range(0, 9)],
                "notes": "parity claim over ℕ; probing small cases"}

    def _brainstormer(self, t, n, user):
        ideas = [
            ("consecutive-product", "n²+n = n(n+1): consecutive integers, one is even, so the product is even."),
            ("parity-cases", "Split on n even/odd; both cases give an even total by direct computation."),
            ("induction", "Base n=0 gives 0; step adds 2n+2, which is even, preserving parity."),
        ]
        name, sketch = ideas[n % len(ideas)]
        return {"strategy_name": name, "key_ideas": [sketch], "proof_sketch": sketch,
                "candidate_lemmas": ["n*(n+1) is even", "n^2+n = n*(n+1)"],
                "risks": "none, elementary", "confidence": 0.9}

    def _strategist(self, t, n, user):
        return {"chosen_strategy": "consecutive-product",
                "main_theorem_informal": "For every natural number n, n^2 + n is even.",
                "lemmas": [
                    {"informal": "For every natural n, n*(n+1) is even.",
                     "sketch": "One of two consecutive naturals is even.", "difficulty": 1},
                    {"informal": "For every natural n, n^2 + n = n*(n+1).",
                     "sketch": "Distributivity / ring identity.", "difficulty": 1},
                ],
                "assembly_note": "Rewrite the goal with the identity lemma, then apply the parity lemma."}

    def _formalizer(self, t, n, user):
        stmts = {
            "lemma_1": ["theorem lemma_1 (n : ℕ) : Evenn (n * (n + 1))",   # broken on purpose
                        "theorem lemma_1 (n : ℕ) : Even (n * (n + 1))"],
            "lemma_2": ["theorem lemma_2 (n : ℕ) : n ^ 2 + n = n * (n + 1)"],
            "lemma_2_a": ["theorem lemma_2_a (n : ℕ) : n ^ 2 = n * n"],
            "lemma_2_b": ["theorem lemma_2_b (n : ℕ) : n * n + n = n * (n + 1)"],
            "thm_main": ["theorem thm_main (n : ℕ) : Even (n ^ 2 + n)"],
        }
        opts = stmts.get(t, [f"theorem {t} : True"])
        return {"lean_statement": opts[min(n, len(opts) - 1)], "faithfulness_note": "direct"}

    def _prover(self, t, n, user):
        bodies = {
            "lemma_1": ["simp", "exact Nat.even_mul_succ_self n"],
            "lemma_2": ["rfl", "decide", "rw [lemma_2_a]\nexact lemma_2_b n"],
            "lemma_2_a": ["rw [sq]"],
            "lemma_2_b": ["ring"],
            "thm_main": ["rw [lemma_2]\nexact lemma_1 n"],
        }
        opts = bodies.get(t, ["trivial"])
        return {"proof": opts[min(n, len(opts) - 1)], "claims_false": False, "why": ""}

    def _critic(self, t, n, user):
        return {"diagnosis": "closing tactic too weak for this goal",
                "fix_hint": "cite the exact Mathlib lemma or split the statement",
                "suggest_decompose": bool(t == "lemma_2" and n >= 1)}

    def _decomposer(self, t, n, user):
        return {"lemmas": [
                    {"informal": "n^2 equals n*n.", "sketch": "definition of squaring"},
                    {"informal": "n*n + n equals n*(n+1).", "sketch": "distributivity"}],
                "recombine_hint": "rewrite with the first sub-lemma, close with the second"}

    def _chef(self, t, n, user):
        if "OUTCOME FACTS" in user:
            return {"report": "See verifier facts in the outcome line; this report is scripted."}
        return {"summary": "round failed", "instructions": "try a different decomposition"}


def demo_llm():
    from .llm import ScriptedLLM
    return ScriptedLLM(DemoScript())
