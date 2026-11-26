"""Tests for the agent-native `blueprint` Lean file inspector."""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from brigade.blueprint import inspect_blueprint
from brigade.cli import main as cli_main

PROJECT_DIR = Path(__file__).resolve().parent.parent


_SAMPLE_DRAFT = """import HJBrigade

namespace HJBrigade

theorem done_hj_2_2 : HJUpper 2 2 2 := by
  exact hj_two_upper 2

theorem open_sperner (A : Word 4 2 → Bool) (hA : IsLineFree A) : wordCard A ≤ natChoose 4 2 := by
  sorry

theorem open_mhj : ∃ D : Nat, D ≥ 1 ∧ MHJUpper 2 D 3 2 := by
  sorry

end HJBrigade
"""


class TestBlueprintInspector(unittest.IsolatedAsyncioTestCase):
    async def test_blueprint_extracts_goals_premises_and_audits_completed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "Draft.lean"
            p.write_text(_SAMPLE_DRAFT, encoding="utf-8")
            report = await inspect_blueprint(PROJECT_DIR, p)

            self.assertTrue(report["compile_ok"], report["errors"])
            self.assertEqual(report["total_theorems"], 3)
            self.assertEqual(report["completed_count"], 1)
            self.assertEqual(report["open_count"], 2)

            items = {it["name"]: it for it in report["items"]}
            self.assertTrue(items["done_hj_2_2"]["axiom_ok"])
            self.assertFalse(items["done_hj_2_2"]["has_sorry"])

            self.assertTrue(items["open_sperner"]["has_sorry"])
            self.assertTrue(items["open_sperner"]["goals"], "Expected trace_state goal for open_sperner")
            self.assertTrue(any("⊢" in g for g in items["open_sperner"]["goals"]))
            self.assertTrue(items["open_sperner"]["premise_hints"])

            self.assertTrue(items["open_mhj"]["has_sorry"])
            self.assertTrue(items["open_mhj"]["goals"], "Expected trace_state goal for open_mhj")

    async def test_blueprint_ignores_sorry_in_docstrings_and_comments(self) -> None:
        doc_with_sorry = """import HJBrigade

/-!
Module note: zero `sorry` and zero `native_decide`.
theorem fake_in_comment : False := by sorry
-/

namespace HJBrigade

-- Wait: theorem comment_only : False := by sorry
theorem clean_thm : HJUpper 2 2 2 := by
  exact hj_two_upper 2

end HJBrigade
"""
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "CleanDoc.lean"
            p.write_text(doc_with_sorry, encoding="utf-8")
            report = await inspect_blueprint(PROJECT_DIR, p)

            self.assertTrue(report["compile_ok"], report["errors"])
            self.assertEqual(report["total_theorems"], 1)
            self.assertEqual(report["completed_count"], 1)
            self.assertEqual(report["open_count"], 0)
            item = report["items"][0]
            self.assertEqual(item["name"], "clean_thm")
            self.assertFalse(item["has_sorry"])
            self.assertTrue(item["axiom_ok"], item["note"])


class TestBlueprintCli(unittest.TestCase):
    def test_cli_blueprint_smoke(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "Draft.lean"
            p.write_text(_SAMPLE_DRAFT, encoding="utf-8")
            rc = cli_main(["--project-dir", str(PROJECT_DIR), "blueprint", str(p)])
            self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
