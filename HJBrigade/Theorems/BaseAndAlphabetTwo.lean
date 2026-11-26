import HJBrigade.Core.Line

/-!
# Base Cases and Exact Theorem `HJ(2, r) = r`

Formalizes:
- `hj_one_color`: `HJUpper 1 k 1`
- `hj_alphabet_one`: `HJUpper 1 1 r` (for `r ≥ 1`)
- `hj_two_upper`: `HJUpper r 2 r` via `fin_pigeonhole` on monotone step words
- `hj_two_lower`: `¬ HJUpper d 2 (d + 1)` via Hamming-weight coloring
- `hj_two_exact`: `HJUpper r 2 r ∧ ¬ HJUpper (r - 1) 2 r` for all `r ≥ 1`
-/

namespace HJBrigade

/-- With 1 color, dimension 1 suffices for any alphabet `k`. -/
theorem hj_one_color (k : Nat) : HJUpper 1 k 1 := by
  intro c
  let L : Line 1 k := ⟨fun _ => none, ⟨⟨0, Nat.zero_lt_succ 0⟩, rfl⟩⟩
  refine ⟨L, ⟨0, Nat.zero_lt_succ 0⟩, ?_⟩
  intro t
  exact Fin.ext (by have := (c (L.eval t)).isLt; omega)

/-- With a 1-letter alphabet, dimension 1 suffices for any positive number of colors `r`. -/
theorem hj_alphabet_one (r : Nat) (_hr : r ≥ 1) : HJUpper 1 1 r := by
  intro c
  let L : Line 1 1 := ⟨fun _ => none, ⟨⟨0, Nat.zero_lt_succ 0⟩, rfl⟩⟩
  refine ⟨L, c (L.eval ⟨0, Nat.zero_lt_succ 0⟩), ?_⟩
  intro t
  have ht : t = ⟨0, Nat.zero_lt_succ 0⟩ := Fin.ext (by have := t.isLt; omega)
  rw [ht]

/-- The `m`-th monotone `{0, 1}` word of length `r`: `m` ones followed by `r - m` zeros. -/
def stepWord (r : Nat) (m : Fin (r + 1)) : Word r 2 :=
  fun i => if i.val < m.val then ⟨1, by decide⟩ else ⟨0, by decide⟩

/-- The combinatorial line connecting `stepWord r a` (at `0`) to `stepWord r b` (at `1`). -/
def stepLine (r : Nat) (a b : Fin (r + 1)) (hab : a.val < b.val) : Line r 2 where
  mask := fun i =>
    if i.val < a.val then some ⟨1, by decide⟩
    else if i.val < b.val then none
    else some ⟨0, by decide⟩
  hasWildcard := by
    have ha : a.val < r := Nat.lt_of_lt_of_le hab (Nat.le_of_lt_succ b.isLt)
    refine ⟨⟨a.val, ha⟩, ?_⟩
    have hnot : ¬ (a.val < a.val) := Nat.lt_irrefl _
    simp [hnot, hab]

theorem stepLine_eval_zero (r : Nat) (a b : Fin (r + 1)) (hab : a.val < b.val) :
    (stepLine r a b hab).eval ⟨0, by decide⟩ = stepWord r a := by
  funext i
  by_cases ha : i.val < a.val
  · simp [Line.eval, evalMask, stepLine, stepWord, ha]
  · by_cases hb : i.val < b.val
    · simp [Line.eval, evalMask, stepLine, stepWord, ha, hb]
    · simp [Line.eval, evalMask, stepLine, stepWord, ha, hb]

theorem stepLine_eval_one (r : Nat) (a b : Fin (r + 1)) (hab : a.val < b.val) :
    (stepLine r a b hab).eval ⟨1, by decide⟩ = stepWord r b := by
  funext i
  by_cases ha : i.val < a.val
  · have hb : i.val < b.val := Nat.lt_trans ha hab
    simp [Line.eval, evalMask, stepLine, stepWord, ha, hb]
  · by_cases hb : i.val < b.val
    · simp [Line.eval, evalMask, stepLine, stepWord, ha, hb]
    · simp [Line.eval, evalMask, stepLine, stepWord, ha, hb]

/-- Upper bound: `HJ(2, r) ≤ r` for every `r`. -/
theorem hj_two_upper (r : Nat) : HJUpper r 2 r := by
  intro c
  obtain ⟨a, b, hab, hcol⟩ := fin_pigeonhole r (fun m => c (stepWord r m))
  refine ⟨stepLine r a b hab, c (stepWord r a), ?_⟩
  intro ⟨tv, htv⟩
  match tv, htv with
  | 0, _ => rw [stepLine_eval_zero]
  | 1, _ => rw [stepLine_eval_one, ← hcol]

def onesCountAux : ∀ (d : Nat), (Fin d → Fin 2) → Nat
  | 0, _ => 0
  | d + 1, w => (w ⟨0, Nat.zero_lt_succ d⟩).val + onesCountAux d (fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-- Hamming weight (number of `1` coordinates) of a binary word. -/
def onesCount {d : Nat} (w : Word d 2) : Nat := onesCountAux d w

private theorem onesCountAux_le : ∀ (d : Nat) (w : Fin d → Fin 2), onesCountAux d w ≤ d
  | 0, _ => Nat.le_refl 0
  | d + 1, w => by
    have h0 : (w ⟨0, Nat.zero_lt_succ d⟩).val ≤ 1 := Nat.le_of_lt_succ (w ⟨0, Nat.zero_lt_succ d⟩).isLt
    have hrest := onesCountAux_le d (fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    simp only [onesCountAux]
    omega

theorem onesCount_le {d : Nat} (w : Word d 2) : onesCount w ≤ d :=
  onesCountAux_le d w

private theorem onesCountAux_mono :
    ∀ (d : Nat) (u v : Fin d → Fin 2),
      (∀ i, (u i).val ≤ (v i).val) → onesCountAux d u ≤ onesCountAux d v
  | 0, _, _, _ => Nat.le_refl 0
  | d + 1, u, v, hle => by
    have h0 := hle ⟨0, Nat.zero_lt_succ d⟩
    have hrest := onesCountAux_mono d
      (fun i => u ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => hle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    simp only [onesCountAux]
    omega

private theorem onesCountAux_lt :
    ∀ (d : Nat) (u v : Fin d → Fin 2),
      (∀ i, (u i).val ≤ (v i).val) →
      (∃ i, (u i).val < (v i).val) →
      onesCountAux d u < onesCountAux d v
  | 0, _, _, _, ⟨i, _⟩ => i.elim0
  | d + 1, u, v, hle, ⟨⟨iv, hiv⟩, hlt⟩ => by
    match iv, hiv, hlt with
    | 0, _, hlt0 =>
      have hrest := onesCountAux_mono d
        (fun i => u ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (fun i => v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (fun i => hle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      simp only [onesCountAux]
      omega
    | iv' + 1, hiv', hlt' =>
      have h0 := hle ⟨0, Nat.zero_lt_succ d⟩
      have hrest := onesCountAux_lt d
        (fun i => u ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (fun i => v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (fun i => hle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        ⟨⟨iv', Nat.lt_of_succ_lt_succ hiv'⟩, hlt'⟩
      simp only [onesCountAux]
      omega

theorem onesCount_eval_lt {d : Nat} (L : Line d 2) :
    onesCount (L.eval ⟨0, by decide⟩) < onesCount (L.eval ⟨1, by decide⟩) := by
  refine onesCountAux_lt d _ _ ?_ ?_
  · intro i
    cases hm : L.mask i with
    | none => simp [Line.eval, evalMask, hm]
    | some a => simp [Line.eval, evalMask, hm]
  · obtain ⟨i, hi⟩ := L.hasWildcard
    refine ⟨i, ?_⟩
    simp [Line.eval, evalMask, hi]

/-- Lower bound: `HJ(2, r) ≥ r`, proved via Hamming-weight coloring. -/
theorem hj_two_lower (d : Nat) : ¬ HJUpper d 2 (d + 1) := by
  intro h
  let c : Word d 2 → Fin (d + 1) := fun w => ⟨onesCount w, Nat.lt_succ_of_le (onesCount_le w)⟩
  obtain ⟨L, _, hL⟩ := h c
  have heq := congrArg Fin.val ((hL ⟨0, by decide⟩).trans (hL ⟨1, by decide⟩).symm)
  change onesCount (L.eval ⟨0, by decide⟩) = onesCount (L.eval ⟨1, by decide⟩) at heq
  have hlt := onesCount_eval_lt L
  omega

/-- Exact Hales–Jewett number for binary alphabets: `HJ(2, r) = r` for all `r ≥ 1`. -/
theorem hj_two_exact (r : Nat) (hr : r ≥ 1) : HJUpper r 2 r ∧ ¬ HJUpper (r - 1) 2 r := by
  refine ⟨hj_two_upper r, ?_⟩
  have heq : (r - 1) + 1 = r := Nat.sub_add_cancel hr
  rw [← heq]
  exact hj_two_lower (r - 1)

end HJBrigade
