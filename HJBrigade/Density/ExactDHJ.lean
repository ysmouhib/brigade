import HJBrigade.Density.Sperner
import HJBrigade.Density.Slice9
import HJBrigade.Density.Fujimura

/-!
# Exact Ternary Density Hales–Jewett Bounds (`c_{d, 3}`)

Machine-checked Polymath-1 finite density bounds for alphabet `k = 3`:
- `c_1_3_exact`: `c_{1, 3} = 2` (upper bound via kernel `decide`)
- `c_2_3_exact`: `c_{2, 3} = 6` (upper bound via `lineFree_slice_bound`)
- `c_3_3_exact`: `c_{3, 3} = 18` & `c_3_3_unique_18` (uniqueness of the 18-point extremal set in `[3]^3`)
- `c_4_3_exact`: `c_{4, 3} = 52` (Polymath-1 exact upper bound via slice uniqueness + vertical complement)
- `c_5_3_upper`, `c_6_3_upper`: upper bounds `156`, `468` (paired with `c_5_3_ge_150`, `c_6_3_ge_450`)
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

def c_3_3_lower_set (w : Word 3 3) : Bool :=
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

private def isLF2 (m : Fin 512) : Bool :=
  decide (IsLineFree (decode2 m))

private def u6Arr (i : Fin 4) : Fin 512 :=
  match i.val with
  | 0 => ⟨238, by decide⟩
  | 1 => ⟨245, by decide⟩
  | 2 => ⟨350, by decide⟩
  | _ => ⟨427, by decide⟩

private theorem c_2_3_eq_6_idx :
    ∀ m : Fin 512, 6 ≤ card2 m → isLF2 m = true → ∃ i : Fin 4, u6Arr i = m :=
  forall_fin512 fun a b c => by
    revert a b c
    decide

private theorem u18_unique_idx :
    ∀ i0 i1 i2 : Fin 4, IsLineFree (glue3 (u6Arr i0) (u6Arr i1) (u6Arr i2)) →
      i0.val = 2 ∧ i1.val = 3 ∧ i2.val = 1 := by
  decide

private theorem glue3_350_427_245 :
    glue3 ⟨350, by decide⟩ ⟨427, by decide⟩ ⟨245, by decide⟩ = c_3_3_lower_set := by
  funext w
  revert w
  decide

private theorem slice_isLineFree {d : Nat} {A : Word (d + 1) 3 → Bool} (hA : IsLineFree A)
    (a : Fin 3) : IsLineFree (fun w => A (consFin a w)) := by
  intro L
  let L' : Line (d + 1) 3 := {
    mask := consFin (some a) L.mask
    hasWildcard := by
      obtain ⟨i, hi⟩ := L.hasWildcard
      exact ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, by simp [consFin, hi]⟩
  }
  obtain ⟨t, ht⟩ := hA L'
  refine ⟨t, ?_⟩
  have hev : L'.eval t = consFin a (L.eval t) := by
    funext ⟨v, hv⟩
    cases v <;> rfl
  rw [hev] at ht
  exact ht

/-- Every 18-point line-free subset of `[3]^3` coincides with the canonical extremal set `c_3_3_lower_set`. -/
theorem c_3_3_unique_18 (B : Word 3 3 → Bool) (hB : IsLineFree B) (h18 : 18 ≤ wordCard B) :
    B = c_3_3_lower_set := by
  let B0 : Word 2 3 → Bool := fun w => B (consFin ⟨0, by decide⟩ w)
  let B1 : Word 2 3 → Bool := fun w => B (consFin ⟨1, by decide⟩ w)
  let B2 : Word 2 3 → Bool := fun w => B (consFin ⟨2, by decide⟩ w)
  have hf0 : IsLineFree B0 := slice_isLineFree hB ⟨0, by decide⟩
  have hf1 : IsLineFree B1 := slice_isLineFree hB ⟨1, by decide⟩
  have hf2 : IsLineFree B2 := slice_isLineFree hB ⟨2, by decide⟩
  have hle0 : wordCard B0 ≤ 6 := c_2_3_upper B0 hf0
  have hle1 : wordCard B1 ≤ 6 := c_2_3_upper B1 hf1
  have hle2 : wordCard B2 ≤ 6 := c_2_3_upper B2 hf2
  have hsum : wordCard B = wordCard B0 + wordCard B1 + wordCard B2 := wordCard_succ3 B
  have h60 : 6 ≤ card2 (encode2 B0) := by rw [← wordCard_eq_card2_encode2 B0]; omega
  have h61 : 6 ≤ card2 (encode2 B1) := by rw [← wordCard_eq_card2_encode2 B1]; omega
  have h62 : 6 ≤ card2 (encode2 B2) := by rw [← wordCard_eq_card2_encode2 B2]; omega
  have hlf0 : isLF2 (encode2 B0) = true := by dsimp [isLF2]; rw [decode2_encode2]; exact decide_eq_true hf0
  have hlf1 : isLF2 (encode2 B1) = true := by dsimp [isLF2]; rw [decode2_encode2]; exact decide_eq_true hf1
  have hlf2 : isLF2 (encode2 B2) = true := by dsimp [isLF2]; rw [decode2_encode2]; exact decide_eq_true hf2
  obtain ⟨i0, hi0⟩ := c_2_3_eq_6_idx (encode2 B0) h60 hlf0
  obtain ⟨i1, hi1⟩ := c_2_3_eq_6_idx (encode2 B1) h61 hlf1
  obtain ⟨i2, hi2⟩ := c_2_3_eq_6_idx (encode2 B2) h62 hlf2
  have hglue : B = glue3 (u6Arr i0) (u6Arr i1) (u6Arr i2) := by
    rw [hi0, hi1, hi2]
    exact eq_glue3 B
  have hB' : IsLineFree (glue3 (u6Arr i0) (u6Arr i1) (u6Arr i2)) := by rwa [← hglue]
  obtain ⟨hv0, hv1, hv2⟩ := u18_unique_idx i0 i1 i2 hB'
  have hu0 : u6Arr i0 = ⟨350, by decide⟩ := by
    have : i0 = ⟨2, by decide⟩ := Fin.ext hv0
    rw [this]; rfl
  have hu1 : u6Arr i1 = ⟨427, by decide⟩ := by
    have : i1 = ⟨3, by decide⟩ := Fin.ext hv1
    rw [this]; rfl
  have hu2 : u6Arr i2 = ⟨245, by decide⟩ := by
    have : i2 = ⟨1, by decide⟩ := Fin.ext hv2
    rw [this]; rfl
  rw [hglue, hu0, hu1, hu2, glue3_350_427_245]

private def vertLine4 (w : Word 3 3) : Line 4 3 where
  mask := consFin none (fun i => some (w i))
  hasWildcard := ⟨⟨0, by decide⟩, rfl⟩

private theorem vertLine4_eval (w : Word 3 3) (t : Fin 3) :
    (vertLine4 w).eval t = consFin t w := by
  funext ⟨v, hv⟩
  cases v <;> rfl

private theorem third_slice_le_9 {A : Word 4 3 → Bool} (hA : IsLineFree A)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : (fun w => A (consFin a w)) = c_3_3_lower_set)
    (hb : (fun w => A (consFin b w)) = c_3_3_lower_set) :
    wordCard (fun w => A (consFin c w)) ≤ 9 := by
  have hcomp : ∀ w : Word 3 3, A (consFin c w) = true → (!c_3_3_lower_set w) = true := by
    intro w hcw
    cases hlow : c_3_3_lower_set w with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨t, ht⟩ := hA (vertLine4 w)
      rw [vertLine4_eval] at ht
      have hta : A (consFin a w) = true := by have := congrFun ha w; rw [this, hlow]
      have htb : A (consFin b w) = true := by have := congrFun hb w; rw [this, hlow]
      have hcases : t = a ∨ t = b ∨ t = c := by
        have := t.isLt; have := a.isLt; have := b.isLt; have := c.isLt
        have hne_ab : a.val ≠ b.val := fun h => hab (Fin.ext h)
        have hne_ac : a.val ≠ c.val := fun h => hac (Fin.ext h)
        have hne_bc : b.val ≠ c.val := fun h => hbc (Fin.ext h)
        rcases (by omega : t.val = a.val ∨ t.val = b.val ∨ t.val = c.val) with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      rcases hcases with rfl | rfl | rfl <;> simp_all
  have hle := wordCard_mono hcomp
  have h9 : wordCard (fun w => !c_3_3_lower_set w) = 9 := by decide
  omega

/-- **Polymath-1 Exact Upper Bound (`c_{4, 3} ≤ 52`)**: no line-free subset of `[3]^4` has size ≥ 53. -/
theorem c_4_3_upper : ∀ A : Word 4 3 → Bool, IsLineFree A → wordCard A ≤ 52 := by
  intro A hA
  let S0 : Word 3 3 → Bool := fun w => A (consFin ⟨0, by decide⟩ w)
  let S1 : Word 3 3 → Bool := fun w => A (consFin ⟨1, by decide⟩ w)
  let S2 : Word 3 3 → Bool := fun w => A (consFin ⟨2, by decide⟩ w)
  have hf0 : IsLineFree S0 := slice_isLineFree hA ⟨0, by decide⟩
  have hf1 : IsLineFree S1 := slice_isLineFree hA ⟨1, by decide⟩
  have hf2 : IsLineFree S2 := slice_isLineFree hA ⟨2, by decide⟩
  have hb0 : wordCard S0 ≤ 18 := c_3_3_upper S0 hf0
  have hb1 : wordCard S1 ≤ 18 := c_3_3_upper S1 hf1
  have hb2 : wordCard S2 ≤ 18 := c_3_3_upper S2 hf2
  have hsum : wordCard A = wordCard S0 + wordCard S1 + wordCard S2 := wordCard_succ3 A
  by_cases hgt : 53 ≤ wordCard A
  · exfalso
    have hpair : (18 ≤ wordCard S0 ∧ 18 ≤ wordCard S1) ∨
        (18 ≤ wordCard S0 ∧ 18 ≤ wordCard S2) ∨
        (18 ≤ wordCard S1 ∧ 18 ≤ wordCard S2) := by omega
    rcases hpair with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
    · have h0eq := c_3_3_unique_18 S0 hf0 h0
      have h1eq := c_3_3_unique_18 S1 hf1 h1
      have h2le := third_slice_le_9 hA ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
        (by decide) (by decide) (by decide) h0eq h1eq
      change wordCard S2 ≤ 9 at h2le
      omega
    · have h0eq := c_3_3_unique_18 S0 hf0 h0
      have h2eq := c_3_3_unique_18 S2 hf2 h2
      have h1le := third_slice_le_9 hA ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩
        (by decide) (by decide) (by decide) h0eq h2eq
      change wordCard S1 ≤ 9 at h1le
      omega
    · have h1eq := c_3_3_unique_18 S1 hf1 h1
      have h2eq := c_3_3_unique_18 S2 hf2 h2
      have h0le := third_slice_le_9 hA ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩
        (by decide) (by decide) (by decide) h1eq h2eq
      change wordCard S0 ≤ 9 at h0le
      omega
  · omega

/-- Exact value `c_{4, 3} = 52` (Polymath-1). -/
theorem c_4_3_exact :
    (∀ A : Word 4 3 → Bool, IsLineFree A → wordCard A ≤ 52) ∧
    (∃ A : Word 4 3 → Bool, IsLineFree A ∧ wordCard A = 52) :=
  ⟨c_4_3_upper, c_4_3_ge_52⟩

theorem c_5_3_upper : ∀ A : Word 5 3 → Bool, IsLineFree A → wordCard A ≤ 156 :=
  lineFree_slice_bound c_4_3_upper

theorem c_6_3_upper : ∀ A : Word 6 3 → Bool, IsLineFree A → wordCard A ≤ 468 :=
  lineFree_slice_bound c_5_3_upper

end HJBrigade
