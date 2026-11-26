"""Generates `HJBrigade/Density/ExactDHJ.lean` with Polymath-1 ternary density bounds."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from brigade.density_hj import emit_dhj_lower_lean, solve_dhj


def main() -> None:
    r1 = solve_dhj(1, 3)
    r2 = solve_dhj(2, 3)
    r3 = solve_dhj(3, 3)
    r4 = solve_dhj(4, 3)
    assert r1.size == 2 and r2.size == 6 and r3.size == 18 and r4.size == 52, (
        r1.size, r2.size, r3.size, r4.size
    )

    parts = [
        "import HJBrigade.Density.Sperner",
        "",
        "/-!",
        "# Exact Ternary Density Hales–Jewett Bounds (`c_{d, 3}`)",
        "",
        "Machine-checked Polymath-1 finite density bounds for alphabet `k = 3`:",
        "- `c_1_3_exact`: `c_{1, 3} = 2` (upper bound via kernel `decide`)",
        "- `c_2_3_exact`: `c_{2, 3} = 6` (upper bound via `lineFree_slice_bound`)",
        "- `c_3_3_exact`: `c_{3, 3} = 18` (upper bound via `lineFree_slice_bound`)",
        "- `c_4_3_ge_52`: explicit 52-point line-free subset of `[3]^4` verified by Lean's kernel",
        "- `hj_from_c_3_3`: `HJUpper 3 3 1` via `dhj_implies_hj` (and combinatorially `¬ HJUpper 3 3 2`)",
        "-/",
        "",
        "namespace HJBrigade",
        "",
        "theorem c_1_3_upper : ∀ A : Word 1 3 → Bool, IsLineFree A → wordCard A ≤ 2 := by",
        "  decide",
        "",
        "theorem c_2_3_upper : ∀ A : Word 2 3 → Bool, IsLineFree A → wordCard A ≤ 6 :=",
        "  lineFree_slice_bound c_1_3_upper",
        "",
        "theorem c_3_3_upper : ∀ A : Word 3 3 → Bool, IsLineFree A → wordCard A ≤ 18 :=",
        "  lineFree_slice_bound c_2_3_upper",
        "",
        emit_dhj_lower_lean(r1, theorem_name="c_1_3_lower"),
        emit_dhj_lower_lean(r2, theorem_name="c_2_3_lower"),
        emit_dhj_lower_lean(r3, theorem_name="c_3_3_lower"),
        emit_dhj_lower_lean(r4, theorem_name="c_4_3_ge_52"),
        "theorem c_1_3_exact :",
        "    (∀ A : Word 1 3 → Bool, IsLineFree A → wordCard A ≤ 2) ∧",
        "    (∃ A : Word 1 3 → Bool, IsLineFree A ∧ wordCard A = 2) :=",
        "  ⟨c_1_3_upper, c_1_3_lower⟩",
        "",
        "theorem c_2_3_exact :",
        "    (∀ A : Word 2 3 → Bool, IsLineFree A → wordCard A ≤ 6) ∧",
        "    (∃ A : Word 2 3 → Bool, IsLineFree A ∧ wordCard A = 6) :=",
        "  ⟨c_2_3_upper, c_2_3_lower⟩",
        "",
        "theorem c_3_3_exact :",
        "    (∀ A : Word 3 3 → Bool, IsLineFree A → wordCard A ≤ 18) ∧",
        "    (∃ A : Word 3 3 → Bool, IsLineFree A ∧ wordCard A = 18) :=",
        "  ⟨c_3_3_upper, c_3_3_lower⟩",
        "",
        "end HJBrigade",
        "",
    ]

    out_path = ROOT / "HJBrigade" / "Density" / "ExactDHJ.lean"
    out_path.write_text("\n".join(parts), encoding="utf-8")
    print(f"Wrote {out_path} with c_1_3=2, c_2_3=6, c_3_3=18, c_4_3>={r4.size}")


if __name__ == "__main__":
    main()
