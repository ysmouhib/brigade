import HJBrigade.Core.FinQuant

/-!
# Combinatorial Words, Combinatorial Lines, and Hales–Jewett Bounds

Canonical formalization of words `[k]^d`, combinatorial lines `Line d k`,
monochromaticity `IsMonoLine`, and the finite Hales–Jewett predicate `HJUpper d k r`.
-/

namespace HJBrigade

/-- A word of length `d` over an alphabet of size `k`. -/
abbrev Word (d k : Nat) := Fin d → Fin k

/-- Evaluate a line mask (`none` = active wildcard coordinate, `some a` = fixed letter `a`)
at letter `t : Fin k`. -/
def evalMask {d k : Nat} (mask : Fin d → Option (Fin k)) (t : Fin k) : Word d k :=
  fun i => (mask i).getD t

/-- A combinatorial line in `[k]^d` specified by a mask with at least one wildcard. -/
structure Line (d k : Nat) where
  mask : Fin d → Option (Fin k)
  hasWildcard : ∃ i : Fin d, mask i = none

def Line.eval {d k : Nat} (L : Line d k) (t : Fin k) : Word d k :=
  evalMask L.mask t

theorem Line.eval_injective {d k : Nat} (L : Line d k) {t₁ t₂ : Fin k}
    (h : L.eval t₁ = L.eval t₂) : t₁ = t₂ := by
  obtain ⟨i, hi⟩ := L.hasWildcard
  have hval := congrFun h i
  simpa [Line.eval, evalMask, hi] using hval

/-- A line `L` is monochromatic under `c` if all `k` points on `L` receive the same color. -/
def IsMonoLine {d k r : Nat} (c : Word d k → Fin r) (L : Line d k) : Prop :=
  ∃ color : Fin r, ∀ t : Fin k, c (L.eval t) = color

def IsMonoMask {d k r : Nat} (c : Word d k → Fin r) (mask : Fin d → Option (Fin k)) : Prop :=
  ∃ color : Fin r, ∀ t : Fin k, c (evalMask mask t) = color

instance {d k r : Nat} (c : Word d k → Fin r) (mask : Fin d → Option (Fin k)) :
    Decidable (IsMonoMask c mask) :=
  inferInstanceAs (Decidable (∃ color : Fin r, ∀ t : Fin k, c (evalMask mask t) = color))

instance {d k r : Nat} (c : Word d k → Fin r) (L : Line d k) :
    Decidable (IsMonoLine c L) :=
  inferInstanceAs (Decidable (∃ color : Fin r, ∀ t : Fin k, c (L.eval t) = color))

/-- `c` contains a monochromatic combinatorial line. -/
def HasMonoLine (d k r : Nat) (c : Word d k → Fin r) : Prop :=
  ∃ L : Line d k, IsMonoLine c L

theorem hasMonoLine_iff_mask (d k r : Nat) (c : Word d k → Fin r) :
    HasMonoLine d k r c ↔ ∃ mask : Fin d → Option (Fin k), (∃ i : Fin d, mask i = none) ∧ IsMonoMask c mask := by
  constructor
  · rintro ⟨⟨mask, hw⟩, hmono⟩
    exact ⟨mask, hw, hmono⟩
  · rintro ⟨mask, hw, hmono⟩
    exact ⟨⟨mask, hw⟩, hmono⟩

instance (d k r : Nat) (c : Word d k → Fin r) : Decidable (HasMonoLine d k r c) :=
  decidable_of_iff (∃ mask : Fin d → Option (Fin k), (∃ i : Fin d, mask i = none) ∧ IsMonoMask c mask)
    (hasMonoLine_iff_mask d k r c).symm

/-- `HJUpper d k r` asserts that every `r`-coloring of `[k]^d` has a monochromatic line. -/
def HJUpper (d k r : Nat) : Prop :=
  ∀ c : Word d k → Fin r, HasMonoLine d k r c

instance (d k r : Nat) : Decidable (HJUpper d k r) :=
  inferInstanceAs (Decidable (∀ c : Word d k → Fin r, HasMonoLine d k r c))

/-- Pad a line in `[k]^d` on the right to dimension `d' ≥ d` with a fixed letter `pad`. -/
def Line.liftPrefix {d d' k : Nat} (hle : d ≤ d') (pad : Fin k) (L : Line d k) : Line d' k where
  mask := fun i =>
    if hi : i.val < d then L.mask ⟨i.val, hi⟩ else some pad
  hasWildcard := by
    obtain ⟨i, hi⟩ := L.hasWildcard
    refine ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩, ?_⟩
    simp [i.isLt, hi]

theorem Line.liftPrefix_eval_lt {d d' k : Nat} (hle : d ≤ d') (pad : Fin k) (L : Line d k)
    (t : Fin k) (i : Fin d) :
    (L.liftPrefix hle pad).eval t ⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩ = L.eval t i := by
  simp [Line.eval, evalMask, Line.liftPrefix, i.isLt]

/-- Monotonicity in dimension: `HJUpper d k r` implies `HJUpper d' k r` for `d ≤ d'` (when `k ≥ 1`). -/
theorem HJUpper.mono_dim {d d' k r : Nat} (hle : d ≤ d') (hk : k ≥ 1) (h : HJUpper d k r) :
    HJUpper d' k r := by
  intro c
  let pad : Fin k := ⟨0, hk⟩
  let cSub : Word d k → Fin r := fun w =>
    c (fun i => if hi : i.val < d then w ⟨i.val, hi⟩ else pad)
  obtain ⟨L, color, hL⟩ := h cSub
  refine ⟨L.liftPrefix hle pad, color, ?_⟩
  intro t
  have hcoord :
      (fun i : Fin d' => if hi : i.val < d then L.eval t ⟨i.val, hi⟩ else pad) =
        (L.liftPrefix hle pad).eval t := by
    funext i
    by_cases hi : i.val < d
    · simp [Line.eval, evalMask, Line.liftPrefix, hi]
    · simp [Line.eval, evalMask, Line.liftPrefix, hi]
  rw [← hcoord]
  exact hL t

/-- Monotonicity in colors: `HJUpper d k r` implies `HJUpper d k r'` for `1 ≤ r' ≤ r`. -/
theorem HJUpper.mono_colors {d k r' r : Nat} (hr' : r' ≥ 1) (hle : r' ≤ r) (h : HJUpper d k r) :
    HJUpper d k r' := by
  intro c
  let cBig : Word d k → Fin r := fun w => ⟨(c w).val, Nat.lt_of_lt_of_le (c w).isLt hle⟩
  obtain ⟨L, _, hL⟩ := h cBig
  by_cases hk : k = 0
  · subst hk
    refine ⟨L, ⟨0, hr'⟩, ?_⟩
    intro t
    exact t.elim0
  · have hkpos : k ≥ 1 := Nat.pos_of_ne_zero hk
    let t0 : Fin k := ⟨0, hkpos⟩
    refine ⟨L, c (L.eval t0), ?_⟩
    intro t
    have heq := (hL t).trans (hL t0).symm
    exact Fin.ext (by simpa [cBig] using congrArg Fin.val heq)

end HJBrigade
