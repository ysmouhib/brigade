import HJBrigade.Core.Line

/-!
# Reduction from Van der Waerden's Theorem to Hales–Jewett

Formalizes finite arithmetic progressions (`HasMonoAP`) and the classic coordinate-sum
projection `wordSum : Word d (k + 1) → Fin (d * k + 1)`:
- `hj_implies_vdw`: `HJUpper d (k + 1) r → HasMonoAP (d * k + 1) (k + 1) r`
- `not_vdw_implies_not_hj`: contrapositive lower-bound transfer
-/

namespace HJBrigade

/-- `HasMonoAP N k r` states that every `r`-coloring of `{0, ..., N - 1}` contains a
monochromatic arithmetic progression of length `k` with step `≥ 1`. -/
def HasMonoAP (N k r : Nat) : Prop :=
  ∀ f : Fin N → Fin r,
    ∃ (a step : Nat), step ≥ 1 ∧ ∃ (hb : a + (k - 1) * step < N) (color : Fin r),
      ∀ t : Fin k, f ⟨a + t.val * step, by
        have ht : t.val ≤ k - 1 := Nat.le_pred_of_lt t.isLt
        have hmul : t.val * step ≤ (k - 1) * step := Nat.mul_le_mul_right step ht
        omega⟩ = color

/-- Bounded decidable predicate that a single coloring `f : Fin N → Fin r` has a monochromatic
arithmetic progression of length `k` with step `≥ 1`. -/
def HasMonoAPFor (N k r : Nat) (f : Fin N → Fin r) : Prop :=
  ∃ (a : Fin (N + 1)) (step : Fin (N + 1)),
    step.val ≥ 1 ∧
    ∃ (_hb : a.val + (k - 1) * step.val < N) (color : Fin r),
      ∀ t : Fin k, f ⟨a.val + t.val * step.val, by
        have ht : t.val ≤ k - 1 := Nat.le_pred_of_lt t.isLt
        have hmul : t.val * step.val ≤ (k - 1) * step.val := Nat.mul_le_mul_right step.val ht
        omega⟩ = color

instance (N k r : Nat) (f : Fin N → Fin r) : Decidable (HasMonoAPFor N k r f) :=
  inferInstanceAs (Decidable (∃ (a : Fin (N + 1)) (step : Fin (N + 1)),
    step.val ≥ 1 ∧ ∃ (_hb : a.val + (k - 1) * step.val < N) (color : Fin r),
      ∀ t : Fin k, f ⟨a.val + t.val * step.val, _⟩ = color))

theorem hasMonoAP_iff_for (N k r : Nat) :
    HasMonoAP N k r ↔ ∀ f : Fin N → Fin r, HasMonoAPFor N k r f := by
  constructor
  · intro h f
    obtain ⟨a, step, hstep, hb, col, hf⟩ := h f
    have ha : a < N + 1 := by omega
    by_cases hk1 : k ≤ 1
    · have h0 : k - 1 = 0 := by omega
      have haN : a + (k - 1) * 1 < N := by
        simp only [h0, Nat.zero_mul, Nat.add_zero] at hb ⊢
        exact hb
      refine ⟨⟨a, ha⟩, ⟨1, by omega⟩, Nat.le_refl 1, haN, col, ?_⟩
      intro t
      have ht0 : t.val = 0 := by omega
      simpa [ht0] using hf t
    · have hkpos : k - 1 ≥ 1 := by omega
      have hmul : step ≤ (k - 1) * step := Nat.le_mul_of_pos_left step hkpos
      have hs : step < N + 1 := by omega
      refine ⟨⟨a, ha⟩, ⟨step, hs⟩, hstep, hb, col, hf⟩
  · intro h f
    obtain ⟨a, step, hstep, hb, col, hf⟩ := h f
    exact ⟨a.val, step.val, hstep, hb, col, hf⟩

instance (N k r : Nat) : Decidable (HasMonoAP N k r) :=
  decidable_of_iff (∀ f : Fin N → Fin r, HasMonoAPFor N k r f) (hasMonoAP_iff_for N k r).symm

def wordSumAux : ∀ (d : Nat) {k : Nat}, (Fin d → Fin k) → Nat
  | 0, _, _ => 0
  | d + 1, _, w => (w ⟨0, Nat.zero_lt_succ d⟩).val + wordSumAux d (fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

def wordSum {d k : Nat} (w : Word d k) : Nat :=
  wordSumAux d w

private theorem wordSumAux_le : ∀ (d k : Nat) (w : Fin d → Fin (k + 1)), wordSumAux d w ≤ d * k
  | 0, _, _ => Nat.zero_le _
  | d + 1, k, w => by
    have h0 : (w ⟨0, Nat.zero_lt_succ d⟩).val ≤ k := Nat.le_of_lt_succ (w ⟨0, Nat.zero_lt_succ d⟩).isLt
    have hrest := wordSumAux_le d k (fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    simp only [wordSumAux, Nat.succ_mul]
    omega

theorem wordSum_le {d k : Nat} (w : Word d (k + 1)) : wordSum w ≤ d * k :=
  wordSumAux_le d k w

def maskBaseAux : ∀ (d : Nat) {k : Nat}, (Fin d → Option (Fin k)) → Nat
  | 0, _, _ => 0
  | d + 1, _, m =>
    (match m ⟨0, Nat.zero_lt_succ d⟩ with | none => 0 | some a => a.val) +
    maskBaseAux d (fun i => m ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

def maskWildAux : ∀ (d : Nat) {k : Nat}, (Fin d → Option (Fin k)) → Nat
  | 0, _, _ => 0
  | d + 1, _, m =>
    (match m ⟨0, Nat.zero_lt_succ d⟩ with | none => 1 | some _ => 0) +
    maskWildAux d (fun i => m ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private theorem wordSumAux_evalMask :
    ∀ (d k : Nat) (m : Fin d → Option (Fin k)) (t : Fin k),
      wordSumAux d (evalMask m t) = maskBaseAux d m + maskWildAux d m * t.val
  | 0, _, _, _ => by simp [wordSumAux, maskBaseAux, maskWildAux]
  | d + 1, k, m, t => by
    have ih := wordSumAux_evalMask d k (fun i => m ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) t
    change ((m 0).getD t).val + wordSumAux d (fun i => evalMask m t ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) =
      (match m 0 with | none => 0 | some a => a.val) +
        maskBaseAux d (fun i => m ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) +
      ((match m 0 with | none => 1 | some _ => 0) +
        maskWildAux d (fun i => m ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) * t.val
    have htail :
        wordSumAux d (fun i => evalMask m t ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) =
          maskBaseAux d (fun i => m ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) +
            maskWildAux d (fun i => m ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) * t.val := ih
    cases hm : m 0 with
    | none =>
      dsimp [Option.getD]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    | some a =>
      dsimp [Option.getD]
      rw [Nat.add_mul, Nat.zero_mul]
      omega

private theorem maskWildAux_pos :
    ∀ (d : Nat) {k : Nat} (m : Fin d → Option (Fin k)),
      (∃ i : Fin d, m i = none) → maskWildAux d m ≥ 1
  | 0, _, _, ⟨i, _⟩ => i.elim0
  | d + 1, _, m, ⟨⟨iv, hiv⟩, hnone⟩ => by
    change (match m 0 with | none => 1 | some _ => 0) +
      maskWildAux d (fun i => m ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ≥ 1
    match iv, hiv, hnone with
    | 0, _, h0 =>
      have h0' : m 0 = none := h0
      rw [h0']
      dsimp
      omega
    | iv' + 1, hiv', hrest =>
      have ih := maskWildAux_pos d (fun i => m ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        ⟨⟨iv', Nat.lt_of_succ_lt_succ hiv'⟩, hrest⟩
      omega

/-- Every combinatorial line in `[k+1]^d` projects via coordinate sum to a non-trivial
arithmetic progression of length `k + 1` in `{0, ..., d * k}`. -/
theorem hj_implies_vdw {d k r : Nat} (h : HJUpper d (k + 1) r) :
    HasMonoAP (d * k + 1) (k + 1) r := by
  intro f
  let c : Word d (k + 1) → Fin r := fun w =>
    f ⟨wordSum w, Nat.lt_succ_of_le (wordSum_le w)⟩
  obtain ⟨L, color, hL⟩ := h c
  let a := maskBaseAux d L.mask
  let step := maskWildAux d L.mask
  have hstep : step ≥ 1 := maskWildAux_pos d L.mask L.hasWildcard
  have hlast_k : a + k * step < d * k + 1 := by
    have heval := wordSumAux_evalMask d (k + 1) L.mask ⟨k, Nat.lt_succ_self k⟩
    have hle := wordSum_le (L.eval ⟨k, Nat.lt_succ_self k⟩)
    change wordSumAux d (evalMask L.mask ⟨k, Nat.lt_succ_self k⟩) ≤ d * k at hle
    change wordSumAux d (evalMask L.mask ⟨k, Nat.lt_succ_self k⟩) = a + step * k at heval
    rw [heval, Nat.mul_comm] at hle
    omega
  have hlast : a + ((k + 1) - 1) * step < d * k + 1 := by
    have hk : (k + 1) - 1 = k := Nat.add_sub_cancel k 1
    rwa [hk]
  refine ⟨a, step, hstep, hlast, color, ?_⟩
  intro t
  have heval := wordSumAux_evalMask d (k + 1) L.mask t
  have hpt : (⟨a + t.val * step, by
      have ht : t.val ≤ k := Nat.le_of_lt_succ t.isLt
      have hmul : t.val * step ≤ k * step := Nat.mul_le_mul_right step ht
      omega⟩ : Fin (d * k + 1)) =
      ⟨wordSum (L.eval t), Nat.lt_succ_of_le (wordSum_le (L.eval t))⟩ := by
    apply Fin.ext
    change a + t.val * step = wordSumAux d (evalMask L.mask t)
    rw [heval, Nat.mul_comm]
  rw [hpt]
  exact hL t

/-- Contrapositive: refuting `HasMonoAP (d * k + 1) (k + 1) r` immediately refutes `HJUpper d (k + 1) r`. -/
theorem not_vdw_implies_not_hj {d k r : Nat} (h : ¬ HasMonoAP (d * k + 1) (k + 1) r) :
    ¬ HJUpper d (k + 1) r :=
  fun hhj => h (hj_implies_vdw hhj)

end HJBrigade
