"""Tests for the combinatorial HJ solver and Lean 4 kernel certificate compilation."""

from __future__ import annotations

from pathlib import Path
import unittest

from brigade.lean_verifier import RealLeanVerifier
from brigade.skeptic_hj import (
    emit_lower_bound_lean,
    emit_upper_bound_lean,
    emit_vdw_lower_lean,
    solve_hj,
    solve_vdw,
)

PROJECT_DIR = Path(__file__).resolve().parent.parent


class TestSkepticAndCertificates(unittest.IsolatedAsyncioTestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.verifier = RealLeanVerifier(PROJECT_DIR, timeout_s=60.0)

    def test_solve_hj_known_small_cases(self) -> None:
        r122 = solve_hj(1, 2, 2)
        self.assertEqual(r122.status, "SAT_LINE_FREE")
        self.assertIsNotNone(r122.witness_coloring)

        r222 = solve_hj(2, 2, 2)
        self.assertEqual(r222.status, "UNSAT_MONO_FORCED")
        self.assertIsNotNone(r222.cert_tree)

        r323 = solve_hj(3, 2, 3)
        self.assertEqual(r323.status, "UNSAT_MONO_FORCED")
        self.assertIsNotNone(r323.root_sym_idx)

        r332 = solve_hj(3, 3, 2)
        self.assertEqual(r332.status, "SAT_LINE_FREE")
        self.assertEqual(len(r332.witness_coloring or []), 27)

        r432 = solve_hj(4, 3, 2)
        self.assertEqual(r432.status, "UNSAT_MONO_FORCED")
        self.assertIsNotNone(r432.cert_tree)

        vdw8 = solve_vdw(8, 3, 2)
        self.assertEqual(vdw8["status"], "SAT_AP_FREE")

    async def test_lean_kernel_verifies_lower_and_upper_certificates(self) -> None:
        # 1. Lower bound ¬ HJUpper 3 3 2 verified in Lean kernel
        res_lb = solve_hj(3, 3, 2)
        code_lb = emit_lower_bound_lean(res_lb, theorem_name="test_hj_3_2_gt_3")
        chk_lb = await self.verifier.check(code_lb)
        self.assertTrue(chk_lb.ok, chk_lb.errors)
        self.assertEqual(chk_lb.sorries, 0)
        aud_lb = await self.verifier.axiom_audit(code_lb, "test_hj_3_2_gt_3")
        self.assertTrue(aud_lb.ok, aud_lb.note)

        # 2. General r=3 symmetry-broken certificate HJUpper 3 2 3 via checkCertSym_sound
        res_ub3 = solve_hj(3, 2, 3)
        code_ub3 = emit_upper_bound_lean(res_ub3, theorem_name="test_hj_2_3_le_3")
        self.assertIn("checkCertSym_sound", code_ub3)
        chk_ub3 = await self.verifier.check(code_ub3)
        self.assertTrue(chk_ub3.ok, chk_ub3.errors)
        self.assertEqual(chk_ub3.sorries, 0)
        aud_ub3 = await self.verifier.axiom_audit(code_ub3, "test_hj_2_3_le_3")
        self.assertTrue(aud_ub3.ok, aud_ub3.note)

        # 3. Upper bound HJUpper 4 3 2 via 441-node CertTree verified in Lean kernel
        res_ub4 = solve_hj(4, 3, 2)
        code_ub4 = emit_upper_bound_lean(res_ub4, theorem_name="test_hj_3_2_le_4")
        chk_ub4 = await self.verifier.check(code_ub4)
        self.assertTrue(chk_ub4.ok, chk_ub4.errors)
        self.assertEqual(chk_ub4.sorries, 0)
        aud_ub4 = await self.verifier.axiom_audit(code_ub4, "test_hj_3_2_le_4")
        self.assertTrue(aud_ub4.ok, aud_ub4.note)

        # 4. Van der Waerden lower bound ¬ HasMonoAP 8 3 2 verified in Lean kernel
        vdw8 = solve_vdw(8, 3, 2)
        code_vdw = emit_vdw_lower_lean(8, 3, 2, vdw8["coloring"], theorem_name="test_vdw_8_3_2")
        chk_vdw = await self.verifier.check(code_vdw)
        self.assertTrue(chk_vdw.ok, chk_vdw.errors)
        aud_vdw = await self.verifier.axiom_audit(code_vdw, "test_vdw_8_3_2")
        self.assertTrue(aud_vdw.ok, aud_vdw.note)

    async def test_shelah_and_vdw_unconditional_theorems_audit(self) -> None:
        code = (
            "theorem test_uncond_hj (k r : Nat) (hk : k ≥ 1) (hr : r ≥ 1) : "
            "∃ d : Nat, d ≥ 1 ∧ HJUpper d k r := by\n"
            "  exact hales_jewett k r hk hr\n\n"
            "theorem test_uncond_vdw (k r : Nat) (hk : k ≥ 1) (hr : r ≥ 1) : "
            "∃ N : Nat, N ≥ 1 ∧ HasMonoAP N k r := by\n"
            "  exact van_der_waerden k r hk hr"
        )
        chk = await self.verifier.check(code)
        self.assertTrue(chk.ok, chk.errors)
        self.assertEqual(chk.sorries, 0)
        aud1 = await self.verifier.axiom_audit(code, "test_uncond_hj")
        aud2 = await self.verifier.axiom_audit(code, "test_uncond_vdw")
        self.assertTrue(aud1.ok, aud1.note)
        self.assertTrue(aud2.ok, aud2.note)


if __name__ == "__main__":
    unittest.main()
