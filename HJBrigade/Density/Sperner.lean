import HJBrigade.Core.Line
import HJBrigade.Theorems.BaseAndAlphabetTwo

/-!
# Finite Density Hales–Jewett Framework, Slice Bounds, and Exact `DHJ(2)` (Sperner's Theorem)

Formalizes:
- `wordCard P`, `IsLineFree A`, `lineFree_slice_bound`
- `dhj_implies_hj`: density bounds below `k^d / r` imply `HJUpper d k r`
- Constructive Symmetric Chain Decomposition (`symChains`) on `Word d 2`
- `sperner_dhj_two` and `dhj_two_exact`: exact maximum line-free density in `[2]^d` is `natChoose d (d / 2)`
-/

namespace HJBrigade

/-- Sum a `Nat`-valued function over `Fin n`. -/
def sumFin : ∀ (n : Nat), (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + sumFin n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem sumFin_mono :
    ∀ (n : Nat) (f g : Fin n → Nat), (∀ i, f i ≤ g i) → sumFin n f ≤ sumFin n g
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, hle => by
    have h0 := hle ⟨0, Nat.zero_lt_succ n⟩
    have hr := sumFin_mono n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => hle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    simp only [sumFin]
    omega

theorem sumFin_le_mul :
    ∀ (n M : Nat) (f : Fin n → Nat), (∀ i, f i ≤ M) → sumFin n f ≤ n * M
  | 0, _, _, _ => Nat.zero_le _
  | n + 1, M, f, hle => by
    have h0 := hle ⟨0, Nat.zero_lt_succ n⟩
    have hr := sumFin_le_mul n M (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => hle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    simp only [sumFin, Nat.succ_mul]
    omega

theorem sumFin_const : ∀ (n c : Nat), sumFin n (fun _ => c) = n * c
  | 0, c => (Nat.zero_mul c).symm
  | n + 1, c => by
    have ih := sumFin_const n c
    simp only [sumFin, ih, Nat.succ_mul]
    omega

theorem sumFin_add :
    ∀ (n : Nat) (f g : Fin n → Nat),
      sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
    have ih := sumFin_add n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    simp only [sumFin]
    omega

theorem sumFin_comm :
    ∀ (m n : Nat) (f : Fin m → Fin n → Nat),
      sumFin m (fun i => sumFin n (fun j => f i j)) =
      sumFin n (fun j => sumFin m (fun i => f i j))
  | 0, n, _ => by
    simp only [sumFin]
    exact (sumFin_const n 0).symm
  | m + 1, n, f => by
    have ih := sumFin_comm m n (fun i j => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ j)
    simp only [sumFin]
    rw [ih, ← sumFin_add]

theorem sumFin_indicator_eq_one :
    ∀ (r : Nat) (x : Fin r), sumFin r (fun col => if x = col then 1 else 0) = 1
  | 0, x => x.elim0
  | r + 1, ⟨xv, hxv⟩ => by
    simp only [sumFin]
    cases xv with
    | zero =>
      have hfun : (fun i : Fin r =>
          if (⟨0, hxv⟩ : Fin (r + 1)) = ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ then 1 else 0) =
          (fun _ : Fin r => 0) := by
        funext i
        simp
      rw [hfun, sumFin_const]
      simp
    | succ xv' =>
      have ih := sumFin_indicator_eq_one r ⟨xv', Nat.lt_of_succ_lt_succ hxv⟩
      have hmatch : (fun i : Fin r =>
          if (⟨xv' + 1, hxv⟩ : Fin (r + 1)) = ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ then 1 else 0) =
          (fun i : Fin r => if (⟨xv', Nat.lt_of_succ_lt_succ hxv⟩ : Fin r) = i then 1 else 0) := by
        funext i
        by_cases hi : (⟨xv', Nat.lt_of_succ_lt_succ hxv⟩ : Fin r) = i
        · have hi' : (⟨xv' + 1, hxv⟩ : Fin (r + 1)) = ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
            apply Fin.ext
            have := congrArg Fin.val hi
            dsimp at this ⊢
            omega
          simp [hi, hi']
        · have hi' : (⟨xv' + 1, hxv⟩ : Fin (r + 1)) ≠ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
            intro h
            apply hi
            apply Fin.ext
            have := congrArg Fin.val h
            dsimp at this ⊢
            omega
          simp [hi, hi']
      rw [hmatch, ih]
      simp

/-- Number of words in `[k]^d` belonging to subset `P : Word d k → Bool`. -/
def wordCard : ∀ {d k : Nat}, (Word d k → Bool) → Nat
  | 0, _, P => if P Fin.elim0 then 1 else 0
  | d + 1, k, P => sumFin k (fun a => wordCard (fun w : Word d k => P (consFin a w)))

theorem wordCard_true : ∀ (d k : Nat), wordCard (d := d) (k := k) (fun _ => true) = k ^ d
  | 0, k => by simp [wordCard]
  | d + 1, k => by
    simp only [wordCard, wordCard_true d k, sumFin_const, Nat.pow_succ, Nat.mul_comm]

theorem wordCard_false : ∀ (d k : Nat), wordCard (d := d) (k := k) (fun _ => false) = 0
  | 0, _ => rfl
  | d + 1, k => by
    simp only [wordCard, wordCard_false d k, sumFin_const, Nat.mul_zero]

theorem wordCard_mono :
    ∀ {d k : Nat} {P Q : Word d k → Bool},
      (∀ w, P w = true → Q w = true) → wordCard P ≤ wordCard Q
  | 0, _, P, Q, h => by
    simp only [wordCard]
    cases hP : P Fin.elim0 with
    | false => exact Nat.zero_le _
    | true => simp [h Fin.elim0 hP]
  | d + 1, k, P, Q, h => by
    simp only [wordCard]
    exact sumFin_mono k _ _ (fun a => wordCard_mono (fun w hw => h (consFin a w) hw))

theorem wordCard_sum_colors :
    ∀ (d k r : Nat) (c : Word d k → Fin r),
      sumFin r (fun col => wordCard (fun w => decide (c w = col))) = k ^ d
  | 0, _, r, c => by
    simp only [wordCard]
    simpa [Nat.pow_zero] using sumFin_indicator_eq_one r (c Fin.elim0)
  | d + 1, k, r, c => by
    simp only [wordCard]
    rw [sumFin_comm r k]
    have hslice : ∀ a : Fin k,
        sumFin r (fun col => wordCard (fun w : Word d k => decide (c (consFin a w) = col))) = k ^ d :=
      fun a => wordCard_sum_colors d k r (fun w => c (consFin a w))
    have hfun : (fun a : Fin k => sumFin r (fun col =>
        wordCard (fun w : Word d k => decide (c (consFin a w) = col)))) =
        (fun _ : Fin k => k ^ d) := funext hslice
    rw [hfun, sumFin_const, Nat.pow_succ, Nat.mul_comm]

/-- A subset `A ⊆ [k]^d` is line-free if every combinatorial line hits at least one point outside `A`. -/
def IsLineFree {d k : Nat} (A : Word d k → Bool) : Prop :=
  ∀ L : Line d k, ∃ t : Fin k, A (L.eval t) = false

theorem isLineFree_iff_mask {d k : Nat} (A : Word d k → Bool) :
    IsLineFree A ↔
      ∀ mask : Fin d → Option (Fin k), (∃ i : Fin d, mask i = none) →
        ∃ t : Fin k, A (evalMask mask t) = false := by
  constructor
  · intro h mask hw
    exact h ⟨mask, hw⟩
  · intro h ⟨mask, hw⟩
    exact h mask hw

instance {d k : Nat} (A : Word d k → Bool) : Decidable (IsLineFree A) :=
  decidable_of_iff
    (∀ mask : Fin d → Option (Fin k), (∃ i : Fin d, mask i = none) →
      ∃ t : Fin k, A (evalMask mask t) = false)
    (isLineFree_iff_mask A).symm

private def consLine {d k : Nat} (a : Fin k) (L : Line d k) : Line (d + 1) k where
  mask := consFin (some a) L.mask
  hasWildcard := by
    obtain ⟨i, hi⟩ := L.hasWildcard
    refine ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, ?_⟩
    simpa [consFin] using hi

private theorem consLine_eval {d k : Nat} (a : Fin k) (L : Line d k) (t : Fin k) :
    (consLine a L).eval t = consFin a (L.eval t) := by
  funext ⟨v, hv⟩
  cases v <;> rfl

/-- Slice submultiplicativity: if every line-free subset of `[k]^d` has size `≤ M`,
then every line-free subset of `[k]^{d+1}` has size `≤ k * M`. -/
theorem lineFree_slice_bound {d k M : Nat}
    (h : ∀ B : Word d k → Bool, IsLineFree B → wordCard B ≤ M)
    (A : Word (d + 1) k → Bool) (hA : IsLineFree A) :
    wordCard A ≤ k * M := by
  simp only [wordCard]
  refine sumFin_le_mul k M _ ?_
  intro a
  refine h (fun w => A (consFin a w)) ?_
  intro L
  obtain ⟨t, ht⟩ := hA (consLine a L)
  rw [consLine_eval] at ht
  exact ⟨t, ht⟩

/-- **Density Hales–Jewett implies Coloring Hales–Jewett**: if every line-free subset of
`[k]^d` has size `≤ M` and `r * M < k ^ d`, then `HJUpper d k r` holds. -/
theorem dhj_implies_hj {d k r M : Nat}
    (hbound : ∀ A : Word d k → Bool, IsLineFree A → wordCard A ≤ M)
    (hlt : r * M < k ^ d) :
    HJUpper d k r := by
  intro c
  letI : Decidable (∃ col : Fin r, M < wordCard (fun w => decide (c w = col))) :=
    decExistsFin r (fun col => M < wordCard (fun w => decide (c w = col)))
  by_cases hex : ∃ col : Fin r, M < wordCard (fun w => decide (c w = col))
  · obtain ⟨col, hbig⟩ := hex
    let Acol : Word d k → Bool := fun w => decide (c w = col)
    have hnot : ¬ IsLineFree Acol := fun hfree => by
      have hle := hbound Acol hfree
      change wordCard (fun w => decide (c w = col)) ≤ M at hle
      omega
    exact Classical.byContradiction fun hno => by
      apply hnot
      intro L
      letI : Decidable (∃ t : Fin k, Acol (L.eval t) = false) :=
        decExistsFin k (fun t => Acol (L.eval t) = false)
      exact Classical.byContradiction fun hno_t => by
        have hall : ∀ t : Fin k, Acol (L.eval t) = true := fun t => by
          cases hval : Acol (L.eval t) with
          | true => rfl
          | false => exact absurd ⟨t, hval⟩ hno_t
        apply hno
        refine ⟨L, col, ?_⟩
        intro t
        have ht := hall t
        simp only [Acol, decide_eq_true_eq] at ht
        exact ht
  · have hle_all : ∀ col : Fin r, wordCard (fun w => decide (c w = col)) ≤ M :=
      fun col => Nat.le_of_not_lt (fun hgt => hex ⟨col, hgt⟩)
    have hsum_le := sumFin_le_mul r M _ hle_all
    rw [wordCard_sum_colors] at hsum_le
    exact absurd hlt (Nat.not_lt_of_ge hsum_le)

/-- Binomial coefficient `C(d, m)` for Sperner's theorem (`DHJ(2)`). -/
def natChoose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | d + 1, m + 1 => natChoose d m + natChoose d (m + 1)

private def extend0 {d : Nat} (w : Word d 2) : Word (d + 1) 2 :=
  consFin ⟨0, Nat.zero_lt_succ 1⟩ w

private def extend1 {d : Nat} (w : Word d 2) : Word (d + 1) 2 :=
  consFin ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ w

private theorem onesCount_extend0 {d : Nat} (w : Word d 2) :
    onesCount (extend0 w) = onesCount w := by
  change (0 : Nat) + onesCountAux d (fun i => extend0 w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) =
    onesCountAux d w
  have htail : (fun i : Fin d => extend0 w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) = w := rfl
  rw [htail, Nat.zero_add]

private theorem onesCount_extend1 {d : Nat} (w : Word d 2) :
    onesCount (extend1 w) = onesCount w + 1 := by
  change (1 : Nat) + onesCountAux d (fun i => extend1 w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) =
    onesCountAux d w + 1
  have htail : (fun i : Fin d => extend1 w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) = w := rfl
  rw [htail, Nat.add_comm]

private theorem wordCard_two {d : Nat} (P : Word (d + 1) 2 → Bool) :
    wordCard P = wordCard (fun w => P (extend0 w)) + wordCard (fun w => P (extend1 w)) := by
  change wordCard (fun w => P (consFin ⟨0, Nat.zero_lt_succ 1⟩ w)) +
      (wordCard (fun w => P (consFin ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ w)) + 0) =
      wordCard (fun w => P (extend0 w)) + wordCard (fun w => P (extend1 w))
  rfl

theorem wordCard_weight :
    ∀ (d m : Nat), wordCard (d := d) (k := 2) (fun w => decide (onesCount w = m)) = natChoose d m
  | 0, 0 => by simp [wordCard, onesCount, onesCountAux, natChoose]
  | 0, m + 1 => by simp [wordCard, onesCount, onesCountAux, natChoose]
  | d + 1, 0 => by
    rw [wordCard_two]
    have h0 : (fun w : Word d 2 => decide (onesCount (extend0 w) = 0)) =
        (fun w => decide (onesCount w = 0)) := by
      funext w; simp [onesCount_extend0]
    have h1 : (fun w : Word d 2 => decide (onesCount (extend1 w) = 0)) =
        (fun _ => false) := by
      funext w; simp [onesCount_extend1]
    rw [h0, h1, wordCard_false d 2, wordCard_weight d 0]
    simp [natChoose]
  | d + 1, m + 1 => by
    rw [wordCard_two]
    have h0 : (fun w : Word d 2 => decide (onesCount (extend0 w) = m + 1)) =
        (fun w => decide (onesCount w = m + 1)) := by
      funext w; simp [onesCount_extend0]
    have h1 : (fun w : Word d 2 => decide (onesCount (extend1 w) = m + 1)) =
        (fun w => decide (onesCount w = m)) := by
      funext w; simp [onesCount_extend1]
    rw [h0, h1, wordCard_weight d (m + 1), wordCard_weight d m, natChoose, Nat.add_comm]

/-- The middle Boolean layer of `[2]^d` (Hamming weight `⌊d/2⌋`). -/
def middleLayer (d : Nat) : Word d 2 → Bool :=
  fun w => decide (onesCount w = d / 2)

theorem middleLayer_card (d : Nat) : wordCard (middleLayer d) = natChoose d (d / 2) :=
  wordCard_weight d (d / 2)

theorem middleLayer_isLineFree (d : Nat) : IsLineFree (middleLayer d) := by
  intro L
  have hlt := onesCount_eval_lt L
  have h0f : (⟨0, by decide⟩ : Fin 2) = 0 := rfl
  have h1f : (⟨1, by decide⟩ : Fin 2) = 1 := rfl
  rw [h0f, h1f] at hlt
  by_cases h0 : onesCount (L.eval 0) = d / 2
  · refine ⟨1, ?_⟩
    simp [middleLayer]
    omega
  · refine ⟨0, ?_⟩
    simp [middleLayer, h0]

-- Symmetric Chain Decomposition on `Word d 2`
private def natRange (start : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => start :: natRange (start + 1) n

private theorem natRange_length (start : Nat) : ∀ m : Nat, (natRange start m).length = m
  | 0 => rfl
  | m + 1 => by simp [natRange, natRange_length (start + 1) m]

private theorem natRange_append_last (a : Nat) :
    ∀ n : Nat, natRange a n ++ [a + n] = natRange a (n + 1)
  | 0 => by simp [natRange]
  | n + 1 => by
    simp only [natRange, List.cons_append]
    have ih := natRange_append_last (a + 1) n
    have heq : a + 1 + n = a + (n + 1) := by omega
    rw [← heq, ih]
    rfl

private def wordLt {d : Nat} (u v : Word d 2) : Prop :=
  (∀ i, (u i).val ≤ (v i).val) ∧ (∃ i, (u i).val < (v i).val)

private theorem wordLt_trans {d : Nat} {u v w : Word d 2}
    (h1 : wordLt u v) (h2 : wordLt v w) : wordLt u w := by
  refine ⟨fun i => Nat.le_trans (h1.1 i) (h2.1 i), ?_⟩
  obtain ⟨i, hi⟩ := h1.2
  exact ⟨i, Nat.lt_of_lt_of_le hi (h2.1 i)⟩

private theorem wordLt_extend0 {d : Nat} {u v : Word d 2} (h : wordLt u v) :
    wordLt (extend0 u) (extend0 v) := by
  refine ⟨fun ⟨idx, hi⟩ => ?_, ?_⟩
  · cases idx with
    | zero => exact Nat.le_refl 0
    | succ idx' => exact h.1 ⟨idx', Nat.lt_of_succ_lt_succ hi⟩
  · obtain ⟨i, hi⟩ := h.2
    exact ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, hi⟩

private theorem wordLt_extend1 {d : Nat} {u v : Word d 2} (h : wordLt u v) :
    wordLt (extend1 u) (extend1 v) := by
  refine ⟨fun ⟨idx, hi⟩ => ?_, ?_⟩
  · cases idx with
    | zero => exact Nat.le_refl 1
    | succ idx' => exact h.1 ⟨idx', Nat.lt_of_succ_lt_succ hi⟩
  · obtain ⟨i, hi⟩ := h.2
    exact ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, hi⟩

private theorem wordLt_extend01 {d : Nat} (w : Word d 2) :
    wordLt (extend0 w) (extend1 w) := by
  refine ⟨fun ⟨idx, hi⟩ => ?_, ?_⟩
  · cases idx with
    | zero => exact Nat.zero_le 1
    | succ _ => exact Nat.le_refl _
  · refine ⟨⟨0, Nat.zero_lt_succ d⟩, ?_⟩
    change (0 : Nat) < 1
    omega

private def lineBetween {d : Nat} (u v : Word d 2) (h : wordLt u v) : Line d 2 where
  mask := fun i => if u i = v i then some (u i) else none
  hasWildcard := by
    obtain ⟨i, hi⟩ := h.2
    refine ⟨i, ?_⟩
    have hne : u i ≠ v i := fun heq => by rw [heq] at hi; exact Nat.lt_irrefl _ hi
    simp [hne]

private theorem lineBetween_eval_zero {d : Nat} (u v : Word d 2) (h : wordLt u v) :
    (lineBetween u v h).eval 0 = u := by
  funext i
  by_cases heq : u i = v i
  · simp [Line.eval, evalMask, lineBetween, heq]
  · have hle := h.1 i
    have hne : (u i).val ≠ (v i).val := fun hv => heq (Fin.ext hv)
    have hu : (u i).val < 2 := (u i).isLt
    have hv : (v i).val < 2 := (v i).isLt
    apply Fin.ext
    dsimp [Line.eval, evalMask, lineBetween]
    simp only [heq, ↓reduceIte, Option.getD_none]
    change 0 = (u i).val
    omega

private theorem lineBetween_eval_one {d : Nat} (u v : Word d 2) (h : wordLt u v) :
    (lineBetween u v h).eval 1 = v := by
  funext i
  by_cases heq : u i = v i
  · simp [Line.eval, evalMask, lineBetween, heq]
  · have hle := h.1 i
    have hne : (u i).val ≠ (v i).val := fun hv => heq (Fin.ext hv)
    have hu : (u i).val < 2 := (u i).isLt
    have hv : (v i).val < 2 := (v i).isLt
    apply Fin.ext
    dsimp [Line.eval, evalMask, lineBetween]
    simp only [heq, ↓reduceIte, Option.getD_none]
    change 1 = (v i).val
    omega

private def splitLast {α : Type u} : List α → Option (List α × α)
  | [] => none
  | [x] => some ([], x)
  | x :: y :: rest =>
    match splitLast (y :: rest) with
    | none => none
    | some (init, last) => some (x :: init, last)

private theorem splitLast_ne_none {α : Type u} :
    ∀ (x y : α) (ys : List α), splitLast (x :: y :: ys) ≠ none
  | _, _, [] => by simp [splitLast]
  | x, y, z :: zs => by
    have ih := splitLast_ne_none y z zs
    change (match splitLast (y :: z :: zs) with
      | none => none
      | some (init, last) => some (x :: init, last)) ≠ none
    cases hs : splitLast (y :: z :: zs) with
    | none => exact absurd hs ih
    | some _ => simp

private theorem splitLast_eq :
    ∀ {α : Type u} (xs init : List α) (last : α),
      splitLast xs = some (init, last) → xs = init ++ [last]
  | _, [], _, _, h => by simp [splitLast] at h
  | _, [x], init, last, h => by
    simp [splitLast] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | _, x :: y :: rest, init, last, h => by
    simp only [splitLast] at h
    cases hs : splitLast (y :: rest) with
    | none => simp [hs] at h
    | some pair =>
      rcases pair with ⟨init', last'⟩
      simp only [hs] at h
      injection h with hp
      have hp' := Prod.ext_iff.mp hp
      have h1 : x :: init' = init := hp'.1
      have h2 : last' = last := hp'.2
      have ih := splitLast_eq (y :: rest) init' last' hs
      rw [← h1, ← h2, List.cons_append, ← ih]

private def stepOneChain {d : Nat} (C : List (Word d 2)) : List (List (Word (d + 1) 2)) :=
  match splitLast C with
  | none => []
  | some ([], x) => [[extend0 x, extend1 x]]
  | some (init, x) => [C.map extend0 ++ [extend1 x], init.map extend1]

private def symChains : (d : Nat) → List (List (Word d 2))
  | 0 => [[Fin.elim0]]
  | d + 1 => (symChains d).flatMap stepOneChain

private def countList {α : Type u} (P : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (if P x then 1 else 0) + countList P xs

private theorem countList_append {α : Type u} (P : α → Bool) :
    ∀ (xs ys : List α), countList P (xs ++ ys) = countList P xs + countList P ys
  | [], ys => by simp [countList]
  | x :: xs, ys => by
    simp only [List.cons_append, countList, countList_append P xs ys]
    omega

private theorem countList_map {α : Type u} {β : Type v} (P : β → Bool) (f : α → β) :
    ∀ (xs : List α), countList P (xs.map f) = countList (fun x => P (f x)) xs
  | [] => rfl
  | x :: xs => by simp [countList, countList_map P f xs]

private def sumChainCounts {α : Type u} (P : α → Bool) : List (List α) → Nat
  | [] => 0
  | C :: Cs => countList P C + sumChainCounts P Cs

private theorem sumChainCounts_append {α : Type u} (P : α → Bool) :
    ∀ (A B : List (List α)), sumChainCounts P (A ++ B) = sumChainCounts P A + sumChainCounts P B
  | [], B => by simp [sumChainCounts]
  | C :: A, B => by
    simp only [List.cons_append, sumChainCounts, sumChainCounts_append P A B]
    omega

private theorem countList_splitLast {α : Type u} (P : α → Bool) (xs init : List α) (last : α)
    (hs : splitLast xs = some (init, last)) :
    countList P xs = countList P init + (if P last then 1 else 0) := by
  rw [splitLast_eq xs init last hs, countList_append]
  simp [countList]

private theorem stepOneChain_count {d : Nat} (P : Word (d + 1) 2 → Bool) :
    ∀ (C : List (Word d 2)),
      sumChainCounts P (stepOneChain C) =
        countList (fun w => P (extend0 w)) C + countList (fun w => P (extend1 w)) C
  | [] => by simp [stepOneChain, splitLast, sumChainCounts, countList]
  | [x] => by
    simp [stepOneChain, splitLast, sumChainCounts, countList]
  | x :: y :: rest => by
    cases hs : splitLast (x :: y :: rest) with
    | none => exact absurd hs (splitLast_ne_none x y rest)
    | some pair =>
      rcases pair with ⟨init, last⟩
      have hC := splitLast_eq (x :: y :: rest) init last hs
      cases init with
      | nil =>
        simp only [List.nil_append] at hC
        injection hC with _ hnil
        exact absurd hnil (List.cons_ne_nil y rest)
      | cons z zs =>
        have hlen0 : countList (fun w => P (extend0 w)) (x :: y :: rest) =
            countList (fun w => P (extend0 w)) (z :: zs) + (if P (extend0 last) then 1 else 0) :=
          countList_splitLast (fun w => P (extend0 w)) (x :: y :: rest) (z :: zs) last hs
        have hlen1 : countList (fun w => P (extend1 w)) (x :: y :: rest) =
            countList (fun w => P (extend1 w)) (z :: zs) + (if P (extend1 last) then 1 else 0) :=
          countList_splitLast (fun w => P (extend1 w)) (x :: y :: rest) (z :: zs) last hs
        have hmap0 : countList P ((x :: y :: rest).map extend0) =
            countList (fun w => P (extend0 w)) (x :: y :: rest) :=
          countList_map P extend0 (x :: y :: rest)
        simp only [stepOneChain, hs, sumChainCounts, countList_append, hmap0, countList_map, Nat.add_zero]
        rw [hlen0, hlen1]
        simp only [countList]
        omega

private theorem symChains_partition :
    ∀ (d : Nat) (P : Word d 2 → Bool),
      sumChainCounts P (symChains d) = wordCard P
  | 0, P => by
    simp [symChains, sumChainCounts, countList, wordCard]
  | d + 1, P => by
    rw [wordCard_two]
    have ih0 := symChains_partition d (fun w => P (extend0 w))
    have ih1 := symChains_partition d (fun w => P (extend1 w))
    rw [← ih0, ← ih1]
    simp only [symChains]
    clear ih0 ih1
    induction symChains d with
    | nil => simp [sumChainCounts]
    | cons C Cs ih =>
      simp only [List.flatMap_cons, sumChainCounts_append, sumChainCounts,
        stepOneChain_count, ih]
      omega

private def IsChain {d : Nat} : List (Word d 2) → Prop
  | [] => True
  | x :: xs => (∀ y ∈ xs, wordLt x y) ∧ IsChain xs

private theorem isChain_map_extend0 {d : Nat} :
    ∀ {xs : List (Word d 2)}, IsChain xs → IsChain (xs.map extend0)
  | [], _ => trivial
  | _ :: xs, ⟨hx, hxs⟩ =>
    ⟨fun y hy => by
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      exact wordLt_extend0 (hx y' hy'),
     isChain_map_extend0 hxs⟩

private theorem isChain_map_extend1 {d : Nat} :
    ∀ {xs : List (Word d 2)}, IsChain xs → IsChain (xs.map extend1)
  | [], _ => trivial
  | _ :: xs, ⟨hx, hxs⟩ =>
    ⟨fun y hy => by
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      exact wordLt_extend1 (hx y' hy'),
     isChain_map_extend1 hxs⟩

private theorem isChain_init_of_append {d : Nat} :
    ∀ {init : List (Word d 2)} {x : Word d 2},
      IsChain (init ++ [x]) → IsChain init ∧ (∀ u ∈ init, wordLt u x)
  | [], _, _ => ⟨trivial, fun _ h => nomatch h⟩
  | u :: rest, x, ⟨hu, hrest⟩ => by
    have ⟨hc, hlast⟩ := isChain_init_of_append hrest
    exact ⟨⟨fun y hy => hu y (List.mem_append_left [x] hy), hc⟩,
      fun z hz => by
        cases hz with
        | head => exact hu x (List.mem_append_right rest (by simp))
        | tail _ hm => exact hlast z hm⟩

private theorem isChain_append_last {d : Nat} :
    ∀ {xs : List (Word d 2)} {z : Word d 2},
      IsChain xs → (∀ u ∈ xs, wordLt u z) → IsChain (xs ++ [z])
  | [], _, _, _ => by
    simp only [List.nil_append]
    exact ⟨(fun _ h => (nomatch h)), trivial⟩
  | u :: xs, z, ⟨hu, hxs⟩, hz =>
    ⟨fun y hy => by
      rcases List.mem_append.mp hy with hmem | hmem
      · exact hu y hmem
      · simp at hmem; subst hmem; exact hz u List.mem_cons_self,
     isChain_append_last hxs (fun w hw => hz w (List.mem_cons_of_mem _ hw))⟩

private theorem stepOneChain_isChain {d : Nat} {C : List (Word d 2)} (hC : IsChain C) :
    ∀ C' ∈ stepOneChain C, IsChain C' := by
  cases hs : splitLast C with
  | none =>
    simp [stepOneChain, hs]
  | some pair =>
    rcases pair with ⟨init, x⟩
    have hEq := splitLast_eq C init x hs
    rw [hEq] at hC
    have ⟨hinit, hlt_x⟩ := isChain_init_of_append hC
    have hall_C : ∀ u ∈ C, wordLt (extend0 u) (extend1 x) := by
      intro u hu
      rw [hEq] at hu
      rcases List.mem_append.mp hu with hmem | hmem
      · exact wordLt_trans (wordLt_extend0 (hlt_x u hmem)) (wordLt_extend01 x)
      · have hux : u = x := List.mem_singleton.mp hmem
        rw [hux]
        exact wordLt_extend01 x
    have hmap0 : IsChain (C.map extend0) := isChain_map_extend0 (by rw [hEq]; exact hC)
    have hlong : IsChain (C.map extend0 ++ [extend1 x]) :=
      isChain_append_last hmap0 (fun y hy => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hy
        exact hall_C u hu)
    cases init with
    | nil =>
      intro C' hmem
      simp only [stepOneChain, hs, List.mem_singleton] at hmem
      subst hmem
      simpa [hEq] using hlong
    | cons y ys =>
      intro C' hmem
      simp only [stepOneChain, hs, List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · exact hlong
      · have hC' : C' = List.map extend1 (y :: ys) := by simpa using hmem'
        rw [hC']
        exact isChain_map_extend1 hinit

private theorem symChains_isChain :
    ∀ (d : Nat) (C : List (Word d 2)), C ∈ symChains d → IsChain C
  | 0, C, h => by
    simp only [symChains, List.mem_singleton] at h
    subst h
    change IsChain [Fin.elim0]
    exact ⟨(fun _ hmem => (nomatch hmem)), trivial⟩
  | d + 1, C, h => by
    simp only [symChains, List.mem_flatMap] at h
    obtain ⟨C0, hC0, hmem⟩ := h
    exact stepOneChain_isChain (symChains_isChain d C0 hC0) C hmem

private theorem countList_chain_le_one {d : Nat} (A : Word d 2 → Bool) (hA : IsLineFree A) :
    ∀ (C : List (Word d 2)), IsChain C → countList A C ≤ 1
  | [], _ => Nat.zero_le 1
  | x :: xs, ⟨hx, hxs⟩ => by
    have ih := countList_chain_le_one A hA xs hxs
    cases hAx : A x with
    | false =>
      simp [countList, hAx]
      exact ih
    | true =>
      have hzero : countList A xs = 0 := by
        clear hxs ih
        induction xs with
        | nil => rfl
        | cons y ys ihy =>
          have hxy := hx y List.mem_cons_self
          have hyFalse : A y = false :=
            Classical.byContradiction fun hnt => by
              have hyTrue : A y = true := by
                cases hyb : A y with
                | true => rfl
                | false => exact absurd hyb hnt
              obtain ⟨⟨tv, htv⟩, hfalse⟩ := hA (lineBetween x y hxy)
              cases tv with
              | zero =>
                have he0 := lineBetween_eval_zero x y hxy
                have h0f : (⟨0, htv⟩ : Fin 2) = 0 := rfl
                rw [h0f, he0, hAx] at hfalse
                simp at hfalse
              | succ tv' =>
                have h1f : (⟨tv' + 1, htv⟩ : Fin 2) = 1 := Fin.ext (by dsimp; omega)
                rw [h1f, lineBetween_eval_one, hyTrue] at hfalse
                simp at hfalse
          have htail := ihy (fun z hz => hx z (List.mem_cons_of_mem _ hz))
          simp [countList, hyFalse, htail]
      simp [countList, hAx, hzero]

private def IsSymRange (d : Nat) (C : List (Word d 2)) : Prop :=
  ∃ a : Nat, 2 * a ≤ d ∧ C.map onesCount = natRange a (d + 1 - 2 * a)

private theorem map_onesCount_extend0 {d : Nat} :
    ∀ (xs : List (Word d 2)), (xs.map extend0).map onesCount = xs.map onesCount
  | [] => rfl
  | _ :: xs => by simp [onesCount_extend0, map_onesCount_extend0 xs]

private theorem map_onesCount_extend1 {d : Nat} :
    ∀ (xs : List (Word d 2)), (xs.map extend1).map onesCount = (xs.map onesCount).map (· + 1)
  | [] => rfl
  | _ :: xs => by simp [onesCount_extend1, map_onesCount_extend1 xs]

private theorem map_succ_natRange (a n : Nat) :
    (natRange a n).map (· + 1) = natRange (a + 1) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [natRange, ih (a + 1)]

private theorem list_append_eq_inj_right (l1 l2 : List Nat) (u v : Nat)
    (h : l1 ++ [u] = l2 ++ [v]) (hl : l1.length = l2.length) : l1 = l2 ∧ u = v := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, and_true] at h
      exact ⟨rfl, h⟩
    | cons _ _ => simp at hl
  | cons a as ih =>
    cases l2 with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.cons_append] at h
      injection h with hab htail
      injection hl with hlt
      obtain ⟨hrest, huv⟩ := ih bs htail hlt
      exact ⟨by rw [hab, hrest], huv⟩

private theorem stepOneChain_symRange {d : Nat} {C : List (Word d 2)} (hC : IsSymRange d C) :
    ∀ C' ∈ stepOneChain C, IsSymRange (d + 1) C' := by
  rcases hC with ⟨a, ha, hmap⟩
  cases hs : splitLast C with
  | none => simp [stepOneChain, hs]
  | some pair =>
    rcases pair with ⟨init, x⟩
    have hEq := splitLast_eq C init x hs
    have hlen : C.length = d + 1 - 2 * a := by
      have hl1 : (C.map onesCount).length = C.length := List.length_map _
      rw [hmap, natRange_length] at hl1
      exact hl1.symm
    have hm1 := hmap
    rw [hEq, List.map_append, List.map_cons, List.map_nil] at hm1
    have hlast_range : natRange a (d + 1 - 2 * a) =
        natRange a (d - 2 * a) ++ [a + (d - 2 * a)] := by
      have hsucc : d + 1 - 2 * a = (d - 2 * a) + 1 := by omega
      rw [hsucc, ← natRange_append_last]
    rw [hlast_range] at hm1
    have hl_init : (init.map onesCount).length = (natRange a (d - 2 * a)).length := by
      have hci : init.length + 1 = C.length := by rw [hEq, List.length_append]; rfl
      rw [List.length_map, natRange_length]
      omega
    obtain ⟨hinit_map, hweight⟩ :=
      list_append_eq_inj_right (init.map onesCount) (natRange a (d - 2 * a))
        (onesCount x) (a + (d - 2 * a)) hm1 hl_init
    have hx_weight : onesCount x = d - a := by omega
    have hlong : IsSymRange (d + 1) (C.map extend0 ++ [extend1 x]) := by
      refine ⟨a, by omega, ?_⟩
      rw [List.map_append, map_onesCount_extend0, hmap, List.map_cons, List.map_nil, onesCount_extend1, hx_weight]
      have h1 : d - a + 1 = a + (d + 1 - 2 * a) := by omega
      have h2 : d + 1 + 1 - 2 * a = (d + 1 - 2 * a) + 1 := by omega
      rw [h1, h2, natRange_append_last]
    cases init with
    | nil =>
      intro C' hmem
      simp only [stepOneChain, hs, List.mem_singleton] at hmem
      subst hmem
      simpa [hEq] using hlong
    | cons y ys =>
      intro C' hmem
      simp only [stepOneChain, hs, List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · exact hlong
      · have hC' : C' = List.map extend1 (y :: ys) := by simpa using hmem'
        rw [hC']
        have hlen_y : (y :: ys).length ≥ 1 := by simp
        have hl2 := hl_init
        rw [List.length_map, natRange_length] at hl2
        refine ⟨a + 1, by omega, ?_⟩
        rw [map_onesCount_extend1, hinit_map, map_succ_natRange]
        have hdim : d + 1 + 1 - 2 * (a + 1) = d - 2 * a := by omega
        rw [hdim]

private theorem symChains_symRange :
    ∀ (d : Nat) (C : List (Word d 2)), C ∈ symChains d → IsSymRange d C
  | 0, C, h => by
    simp only [symChains, List.mem_singleton] at h
    subst h
    exact ⟨0, Nat.le_refl 0, by simp [onesCount, onesCountAux, natRange]⟩
  | d + 1, C, h => by
    simp only [symChains, List.mem_flatMap] at h
    obtain ⟨C0, hC0, hmem⟩ := h
    exact stepOneChain_symRange (symChains_symRange d C0 hC0) C hmem

private theorem mem_natRange_iff (k a n : Nat) :
    k ∈ natRange a n ↔ a ≤ k ∧ k < a + n := by
  induction n generalizing a with
  | zero => simp [natRange]
  | succ n ih =>
    simp only [natRange, List.mem_cons, ih (a + 1)]
    omega

private theorem countList_middle_ge_one {d : Nat} (C : List (Word d 2)) (hC : IsSymRange d C) :
    1 ≤ countList (middleLayer d) C := by
  rcases hC with ⟨a, ha, hmap⟩
  have hmem_range : d / 2 ∈ natRange a (d + 1 - 2 * a) := by
    rw [mem_natRange_iff]
    omega
  rw [← hmap, List.mem_map] at hmem_range
  obtain ⟨w, hw_mem, hw_cnt⟩ := hmem_range
  clear hmap
  induction C with
  | nil => nomatch hw_mem
  | cons u us ih =>
    cases hw_mem with
    | head =>
      simp [countList, middleLayer, hw_cnt]
    | tail _ hm =>
      have := ih hm
      simp only [countList]
      omega

private theorem sumChainCounts_le_of_all {α : Type u} (P : α → Bool) :
    ∀ (Ls : List (List α)), (∀ C ∈ Ls, countList P C ≤ 1) → sumChainCounts P Ls ≤ Ls.length
  | [], _ => Nat.le_refl 0
  | C :: Cs, h => by
    have hc := h C List.mem_cons_self
    have hcs := sumChainCounts_le_of_all P Cs (fun C' hC' => h C' (List.mem_cons_of_mem _ hC'))
    simp only [sumChainCounts, List.length_cons]
    omega

private theorem length_le_sumChainCounts_of_all {α : Type u} (P : α → Bool) :
    ∀ (Ls : List (List α)), (∀ C ∈ Ls, 1 ≤ countList P C) → Ls.length ≤ sumChainCounts P Ls
  | [], _ => Nat.le_refl 0
  | C :: Cs, h => by
    have hc := h C List.mem_cons_self
    have hcs := length_le_sumChainCounts_of_all P Cs (fun C' hC' => h C' (List.mem_cons_of_mem _ hC'))
    simp only [sumChainCounts, List.length_cons]
    omega

/-- **Sperner's Theorem (`DHJ(2)` Upper Bound)**: every line-free subset of `[2]^d`
has cardinality at most `C(d, ⌊d/2⌋)`. -/
theorem sperner_dhj_two (d : Nat) (A : Word d 2 → Bool) (hA : IsLineFree A) :
    wordCard A ≤ natChoose d (d / 2) := by
  rw [← middleLayer_card d, ← symChains_partition d A, ← symChains_partition d (middleLayer d)]
  have h1 := sumChainCounts_le_of_all A (symChains d)
    (fun C hC => countList_chain_le_one A hA C (symChains_isChain d C hC))
  have h2 := length_le_sumChainCounts_of_all (middleLayer d) (symChains d)
    (fun C hC => countList_middle_ge_one C (symChains_symRange d C hC))
  exact Nat.le_trans h1 h2

/-- Exact binary Density Hales–Jewett theorem: `c_{d, 2} = C(d, ⌊d/2⌋)` for all `d`. -/
theorem dhj_two_exact (d : Nat) :
    (∀ A : Word d 2 → Bool, IsLineFree A → wordCard A ≤ natChoose d (d / 2)) ∧
    (∃ A : Word d 2 → Bool, IsLineFree A ∧ wordCard A = natChoose d (d / 2)) :=
  ⟨sperner_dhj_two d, ⟨middleLayer d, middleLayer_isLineFree d, middleLayer_card d⟩⟩

end HJBrigade
