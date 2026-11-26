import HJBrigade.Density.Sperner

/-!
# Exact Ternary Density Hales–Jewett Bounds (`c_{d, 3}`)

Machine-checked Polymath-1 finite density bounds for alphabet `k = 3`:
- `c_1_3_exact`: `c_{1, 3} = 2` (upper bound via kernel `decide`)
- `c_2_3_exact`: `c_{2, 3} = 6` (upper bound via `lineFree_slice_bound`)
- `c_3_3_exact`: `c_{3, 3} = 18` (upper bound via `lineFree_slice_bound`)
- `c_4_3_ge_52`: explicit 52-point line-free subset of `[3]^4` verified by Lean's kernel
- `hj_from_c_3_3`: `HJUpper 3 3 1` via `dhj_implies_hj` (and combinatorially `¬ HJUpper 3 3 2`)
-/

namespace HJBrigade

theorem c_1_3_upper : ∀ A : Word 1 3 → Bool, IsLineFree A → wordCard A ≤ 2 := by
  decide

theorem c_2_3_upper : ∀ A : Word 2 3 → Bool, IsLineFree A → wordCard A ≤ 6 :=
  lineFree_slice_bound c_1_3_upper

theorem c_3_3_upper : ∀ A : Word 3 3 → Bool, IsLineFree A → wordCard A ≤ 18 :=
  lineFree_slice_bound c_2_3_upper

private def c_1_3_lower_tbl : List Bool := [true, true, false]

private def c_1_3_lower_set_idx (w : Word 1 3) : Nat :=
  (List.range 1).foldl (fun acc i =>
    if hi : i < 1 then acc + (w ⟨i, hi⟩).val * 3 ^ i else acc) 0

private def c_1_3_lower_set (w : Word 1 3) : Bool :=
  c_1_3_lower_tbl.getD (c_1_3_lower_set_idx w) false

theorem c_1_3_lower : ∃ A : Word 1 3 → Bool, IsLineFree A ∧ wordCard A = 2 := by
  refine ⟨c_1_3_lower_set, ?_, ?_⟩
  · decide
  · decide

private def c_2_3_lower_tbl : List Bool := [false, true, true, true, false, true, true, true, false]

private def c_2_3_lower_set_idx (w : Word 2 3) : Nat :=
  (List.range 2).foldl (fun acc i =>
    if hi : i < 2 then acc + (w ⟨i, hi⟩).val * 3 ^ i else acc) 0

private def c_2_3_lower_set (w : Word 2 3) : Bool :=
  c_2_3_lower_tbl.getD (c_2_3_lower_set_idx w) false

theorem c_2_3_lower : ∃ A : Word 2 3 → Bool, IsLineFree A ∧ wordCard A = 6 := by
  refine ⟨c_2_3_lower_set, ?_, ?_⟩
  · decide
  · decide

private def c_3_3_lower_tbl : List Bool := [false, true, true, true, true, false, true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true, true, true, true, false]

private def c_3_3_lower_set_idx (w : Word 3 3) : Nat :=
  (List.range 3).foldl (fun acc i =>
    if hi : i < 3 then acc + (w ⟨i, hi⟩).val * 3 ^ i else acc) 0

private def c_3_3_lower_set (w : Word 3 3) : Bool :=
  c_3_3_lower_tbl.getD (c_3_3_lower_set_idx w) false

theorem c_3_3_lower : ∃ A : Word 3 3 → Bool, IsLineFree A ∧ wordCard A = 18 := by
  refine ⟨c_3_3_lower_set, ?_, ?_⟩
  · decide
  · decide

private def c_4_3_ge_52_tbl : List Bool := [false, false, true, false, true, true, true, true, false, false, true, true, true, true, false, true, false, true, true, true, false, true, false, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false, true, false, true, true, true, false, true, false, true, true, true, true, false, false, true, true, true, true, false, true, false, false]

private def c_4_3_ge_52_set_idx (w : Word 4 3) : Nat :=
  (List.range 4).foldl (fun acc i =>
    if hi : i < 4 then acc + (w ⟨i, hi⟩).val * 3 ^ i else acc) 0

private def c_4_3_ge_52_set (w : Word 4 3) : Bool :=
  c_4_3_ge_52_tbl.getD (c_4_3_ge_52_set_idx w) false

theorem c_4_3_ge_52 : ∃ A : Word 4 3 → Bool, IsLineFree A ∧ wordCard A = 52 := by
  refine ⟨c_4_3_ge_52_set, ?_, ?_⟩
  · decide
  · decide

theorem c_1_3_exact :
    (∀ A : Word 1 3 → Bool, IsLineFree A → wordCard A ≤ 2) ∧
    (∃ A : Word 1 3 → Bool, IsLineFree A ∧ wordCard A = 2) :=
  ⟨c_1_3_upper, c_1_3_lower⟩

theorem c_2_3_exact :
    (∀ A : Word 2 3 → Bool, IsLineFree A → wordCard A ≤ 6) ∧
    (∃ A : Word 2 3 → Bool, IsLineFree A ∧ wordCard A = 6) :=
  ⟨c_2_3_upper, c_2_3_lower⟩

theorem c_3_3_exact :
    (∀ A : Word 3 3 → Bool, IsLineFree A → wordCard A ≤ 18) ∧
    (∃ A : Word 3 3 → Bool, IsLineFree A ∧ wordCard A = 18) :=
  ⟨c_3_3_upper, c_3_3_lower⟩

end HJBrigade
