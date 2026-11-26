"""Tests for Multidimensional HJ, Sperner DHJ(2), Polymath-1 ExactDHJ/Fujimura, Moser numbers, and higher HJ bounds."""

from __future__ import annotations

from pathlib import Path
import unittest

from brigade.cli import main as cli_main
from brigade.density_hj import (
    emit_dhj_lower_lean,
    emit_moser_lower_lean,
    solve_dhj,
    solve_fujimura,
    solve_moser,
)
from brigade.lean_verifier import RealLeanVerifier

PROJECT_DIR = Path(__file__).resolve().parent.parent


class TestDensityAndMultidimensionalHJ(unittest.IsolatedAsyncioTestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.verifier = RealLeanVerifier(PROJECT_DIR, timeout_s=60.0)

    def test_solve_dhj_and_fujimura_values(self) -> None:
        r1 = solve_dhj(1, 3)
        r2 = solve_dhj(2, 3)
        r3 = solve_dhj(3, 3)
        r4 = solve_dhj(4, 3)
        r5 = solve_dhj(5, 3)
        r6 = solve_dhj(6, 3)
        self.assertEqual((r1.size, r1.optimal), (2, True))
        self.assertEqual((r2.size, r2.optimal), (6, True))
        self.assertEqual((r3.size, r3.optimal), (18, True))
        self.assertEqual(r4.size, 52)
        self.assertEqual(r5.size, 150)
        self.assertEqual(r6.size, 450)
        self.assertIsNotNone(r5.fujimura_triples)
        self.assertEqual(solve_fujimura(5)[0], 150)
        self.assertEqual(solve_fujimura(6)[0], 450)

    def test_solve_moser_finds_exact_and_known_bounds(self) -> None:
        m1 = solve_moser(1)
        m2 = solve_moser(2)
        m3 = solve_moser(3)
        m4 = solve_moser(4)
        self.assertEqual((m1.size, m1.optimal), (2, True))
        self.assertEqual((m2.size, m2.optimal), (6, True))
        self.assertEqual((m3.size, m3.optimal), (16, True))
        self.assertEqual(m4.size, 43)

    async def test_mhj_sperner_dhj_moser_and_exact_bounds_audit(self) -> None:
        code = (
            "theorem test_mhj (m k r : Nat) (hm : m ≥ 1) (hk : k ≥ 1) (hr : r ≥ 1) :\n"
            "    ∃ D : Nat, D ≥ 1 ∧ MHJUpper m D k r := by\n"
            "  exact multidimensional_hales_jewett m k r hm hk hr\n\n"
            "theorem test_sperner_6 (A : Word 6 2 → Bool) (hA : IsLineFree A) :\n"
            "    wordCard A ≤ natChoose 6 3 := by\n"
            "  exact sperner_dhj_two 6 A hA\n\n"
            "theorem test_dhj_transfer : HJUpper 2 3 1 := by\n"
            "  exact dhj_implies_hj c_2_3_upper (by decide)\n\n"
            "theorem test_c43_exact : (∀ A : Word 4 3 → Bool, IsLineFree A → wordCard A ≤ 52) ∧\n"
            "    (∃ A : Word 4 3 → Bool, IsLineFree A ∧ wordCard A = 52) := by\n"
            "  exact c_4_3_exact\n\n"
            "theorem test_c53_c63 : (∃ A : Word 5 3 → Bool, IsLineFree A ∧ wordCard A = 150) ∧\n"
            "    (∃ B : Word 6 3 → Bool, IsLineFree B ∧ wordCard B = 450) := by\n"
            "  exact ⟨c_5_3_ge_150, c_6_3_ge_450⟩\n\n"
            "theorem test_moser : (∀ B : Word 3 3 → Bool, IsGeomLineFree B → wordCard B ≤ 16) ∧\n"
            "    (∃ A : Word 4 3 → Bool, IsGeomLineFree A ∧ wordCard A = 43) := by\n"
            "  exact ⟨moser_3_3_upper, moser_4_3_ge_43⟩\n\n"
            "theorem test_higher_hj_lb : ¬ HJUpper 4 4 2 ∧ ¬ HJUpper 4 3 3 := by\n"
            "  exact ⟨hj_4_2_gt_4, hj_3_3_gt_4⟩\n\n"
            "theorem test_c33_check : wordCard (middleLayer 4) = 6 := by\n"
            "  decide"
        )
        chk = await self.verifier.check(code)
        self.assertTrue(chk.ok, chk.errors)
        self.assertEqual(chk.sorries, 0)
        for name in (
            "test_mhj",
            "test_sperner_6",
            "test_dhj_transfer",
            "test_c43_exact",
            "test_c53_c63",
            "test_moser",
            "test_higher_hj_lb",
            "test_c33_check",
        ):
            aud = await self.verifier.axiom_audit(code, name)
            self.assertTrue(aud.ok, f"{name}: {aud.note}")

    async def test_emit_dhj_and_moser_lower_lean_verify_in_kernel(self) -> None:
        r2 = solve_dhj(2, 3)
        src2 = emit_dhj_lower_lean(r2, theorem_name="test_dhj_2_3_ge_6")
        chk2 = await self.verifier.check(src2)
        self.assertTrue(chk2.ok, chk2.errors)
        self.assertTrue((await self.verifier.axiom_audit(src2, "test_dhj_2_3_ge_6")).ok)

        m4 = solve_moser(4)
        src4 = emit_moser_lower_lean(m4, theorem_name="test_moser_4_3_ge_43")
        chk4 = await self.verifier.check(src4)
        self.assertTrue(chk4.ok, chk4.errors)
        self.assertTrue((await self.verifier.axiom_audit(src4, "test_moser_4_3_ge_43")).ok)

    def test_cli_certify_dhj_and_moser_smoke(self) -> None:
        rc1 = cli_main(["--project-dir", str(PROJECT_DIR), "certify-dhj", "--d", "5", "--k", "3", "--verify"])
        self.assertEqual(rc1, 0)
        rc2 = cli_main(["--project-dir", str(PROJECT_DIR), "certify-moser", "--d", "4", "--verify"])
        self.assertEqual(rc2, 0)


if __name__ == "__main__":
    unittest.main()
