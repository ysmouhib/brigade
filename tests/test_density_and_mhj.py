"""Tests for Multidimensional HJ, Sperner DHJ(2), dhj_implies_hj, and Polymath-1 ExactDHJ bounds."""

from __future__ import annotations

from pathlib import Path
import unittest

from brigade.cli import main as cli_main
from brigade.density_hj import emit_dhj_lower_lean, solve_dhj
from brigade.lean_verifier import RealLeanVerifier

PROJECT_DIR = Path(__file__).resolve().parent.parent


class TestDensityAndMultidimensionalHJ(unittest.IsolatedAsyncioTestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.verifier = RealLeanVerifier(PROJECT_DIR, timeout_s=60.0)

    def test_solve_dhj_finds_polymath1_values(self) -> None:
        r1 = solve_dhj(1, 3)
        r2 = solve_dhj(2, 3)
        r3 = solve_dhj(3, 3)
        r4 = solve_dhj(4, 3)
        self.assertEqual((r1.size, r1.optimal), (2, True))
        self.assertEqual((r2.size, r2.optimal), (6, True))
        self.assertEqual((r3.size, r3.optimal), (18, True))
        self.assertEqual(r4.size, 52)

    async def test_mhj_and_sperner_and_dhj_theorems_audit(self) -> None:
        code = (
            "theorem test_mhj (m k r : Nat) (hm : m ≥ 1) (hk : k ≥ 1) (hr : r ≥ 1) :\n"
            "    ∃ D : Nat, D ≥ 1 ∧ MHJUpper m D k r := by\n"
            "  exact multidimensional_hales_jewett m k r hm hk hr\n\n"
            "theorem test_sperner_6 (A : Word 6 2 → Bool) (hA : IsLineFree A) :\n"
            "    wordCard A ≤ natChoose 6 3 := by\n"
            "  exact sperner_dhj_two 6 A hA\n\n"
            "theorem test_dhj_transfer : HJUpper 2 3 1 := by\n"
            "  exact dhj_implies_hj c_2_3_upper (by decide)\n\n"
            "theorem test_c33_check : wordCard (middleLayer 4) = 6 := by\n"
            "  decide"
        )
        chk = await self.verifier.check(code)
        self.assertTrue(chk.ok, chk.errors)
        self.assertEqual(chk.sorries, 0)
        for name in ("test_mhj", "test_sperner_6", "test_dhj_transfer", "test_c33_check"):
            aud = await self.verifier.axiom_audit(code, name)
            self.assertTrue(aud.ok, f"{name}: {aud.note}")

    async def test_emit_dhj_lower_lean_verifies_in_kernel(self) -> None:
        res = solve_dhj(2, 3)
        src = emit_dhj_lower_lean(res, theorem_name="test_dhj_2_3_ge_6")
        chk = await self.verifier.check(src)
        self.assertTrue(chk.ok, chk.errors)
        self.assertEqual(chk.sorries, 0)
        aud = await self.verifier.axiom_audit(src, "test_dhj_2_3_ge_6")
        self.assertTrue(aud.ok, aud.note)

    def test_cli_certify_dhj_smoke(self) -> None:
        rc = cli_main(["--project-dir", str(PROJECT_DIR), "certify-dhj", "--d", "2", "--k", "3", "--verify"])
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
