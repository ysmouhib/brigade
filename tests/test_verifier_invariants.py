"""Tests for soundness invariants I1, I2, I4 against real Lean 4.35.0."""

from __future__ import annotations

from pathlib import Path
import unittest

from brigade.lean_verifier import RealLeanVerifier, lint_proof

PROJECT_DIR = Path(__file__).resolve().parent.parent


class TestVerifierInvariants(unittest.IsolatedAsyncioTestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.verifier = RealLeanVerifier(PROJECT_DIR, timeout_s=60.0)

    def test_lint_i4_catches_forbidden_and_allows_decide(self) -> None:
        for bad in [
            "sorry",
            "admit",
            "axiom foo : True",
            "native_decide",
            "sorryAx",
            "unsafe def x := 1",
            "opaque y : Nat",
            "partial def z := z",
            "@[implemented_by foo]",
            "exact Lean.ofReduceBool true",
        ]:
            hits = lint_proof(bad)
            self.assertTrue(hits, f"Expected I4 lint rejection for: {bad}")

        # Kernel-checked `decide`, single-line comments, and nested docstrings must be allowed
        self.assertEqual(lint_proof("-- no sorry used\n/-! nested /- sorry -/ native_decide -/\ndecide"), [])
        self.assertEqual(lint_proof("exact hj_two_upper 3"), [])

    async def test_check_statement_extracts_elaborated_goal_state(self) -> None:
        res = await self.verifier.check_statement("theorem test_goal_extract (n : Nat) : n ≤ n + 1")
        self.assertTrue(res.ok, res.errors)
        self.assertEqual(res.sorries, 1)
        self.assertTrue(res.goals, f"Expected trace_state goal, got raw: {res.raw_output}")
        self.assertTrue(any("⊢" in g and "n + 1" in g for g in res.goals), res.goals)

    async def test_real_lean_check_accepts_valid_and_rejects_sorry(self) -> None:
        good = "theorem test_hj_two_3 : HJUpper 3 2 3 := by\n  exact hj_two_upper 3"
        res_ok = await self.verifier.check(good)
        self.assertTrue(res_ok.ok, res_ok.errors)
        self.assertEqual(res_ok.sorries, 0)

        with_sorry = "theorem test_gate_goal (n : Nat) : n ≤ n + 1 := by\n  sorry"
        res_sorry = await self.verifier.check(with_sorry)
        self.assertTrue(res_sorry.ok)
        self.assertEqual(res_sorry.sorries, 1)

        broken = "theorem test_broken : HJUpper 1 2 2 := by\n  exact hj_two_upper 2"
        res_err = await self.verifier.check(broken)
        self.assertFalse(res_err.ok)
        self.assertTrue(res_err.errors)

    async def test_axiom_audit_i2_enforces_standard_axioms_only(self) -> None:
        good = "theorem test_audit_ok : HJUpper 2 2 2 := by\n  exact hj_two_upper 2"
        aud_ok = await self.verifier.axiom_audit(good, "test_audit_ok")
        self.assertTrue(aud_ok.ok, aud_ok.note)

        # native_decide is caught both by lint_proof AND if bypassed, by Lean.ofReduceBool
        native_code = "theorem test_native : 1 + 1 = 2 := by\n  native_decide"
        aud_native = await self.verifier.axiom_audit(native_code, "test_native")
        self.assertFalse(aud_native.ok)

        # Direct `#print axioms` check on native_decide even without lint confirms non-standard axiom
        res_raw = await self.verifier.check(native_code + "\n#print axioms test_native")
        self.assertTrue(
            "native_decide" in res_raw.raw_output or "Lean.ofReduceBool" in res_raw.raw_output,
            res_raw.raw_output,
        )

        # Custom axiom smuggling is caught
        axiom_code = "axiom cheat_hj : HJUpper 1 3 2\ntheorem test_cheat : HJUpper 1 3 2 := cheat_hj"
        aud_ax = await self.verifier.axiom_audit(axiom_code, "test_cheat")
        self.assertFalse(aud_ax.ok)


if __name__ == "__main__":
    unittest.main()
