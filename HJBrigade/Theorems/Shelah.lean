import HJBrigade.Core.FinEncode
import HJBrigade.Theorems.BaseAndAlphabetTwo
import HJBrigade.Theorems.ColorFocusing
import HJBrigade.Reductions.VanDerWaerden

/-!
# Shelah's Primitive-Recursive Hales–Jewett & Van der Waerden Theorems

Formalizes Saharon Shelah's (1988) constructive cube / equal-ends proof of the
Hales–Jewett theorem for arbitrary finite alphabets `k ≥ 1` and colorings `r ≥ 1`,
with explicit primitive-recursive dimension bound `shelahHJDim k r`, plus the full
unconditional `van_der_waerden` theorem via `hj_implies_vdw`.

Zero `sorry`, zero `native_decide`, standard Lean axioms only.
-/

namespace HJBrigade

private theorem pow_pos_of_pos (r : Nat) (hr : r ≥ 1) : ∀ n : Nat, r ^ n ≥ 1
  | 0 => by simp
  | n + 1 => by
    have ih := pow_pos_of_pos r hr n
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih hr

/-- Dimension bound for Shelah's Cube Lemma (`EqualEnds` on an `m`-dimensional subspace
over a `(k + 1)`-letter alphabet with `r` colors). -/
def shelahCubeDim : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | m + 1, k, r =>
    let N := r ^ ((k + 1) ^ m)
    let R := r ^ ((k + 1) ^ N)
    N + shelahCubeDim m k R

/-- Explicit primitive-recursive Hales–Jewett dimension bound `HJ(k, r) ≤ shelahHJDim k r`. -/
def shelahHJDim : Nat → Nat → Nat
  | 0, _ => 1
  | 1, _ => 1
  | k + 2, r => shelahCubeDim (shelahHJDim (k + 1) r) (k + 1) r

theorem shelahCubeDim_pos : ∀ (m k r : Nat), r ≥ 1 → m ≥ 1 → shelahCubeDim m k r ≥ 1
  | 0, _, _, _, hm => by omega
  | m + 1, k, r, hr, _ => by
    simp only [shelahCubeDim]
    have hN : r ^ ((k + 1) ^ m) ≥ 1 := pow_pos_of_pos r hr _
    omega

theorem shelahHJDim_pos : ∀ (k r : Nat), r ≥ 1 → shelahHJDim k r ≥ 1
  | 0, _, _ => Nat.le_refl 1
  | 1, _, _ => Nat.le_refl 1
  | k + 2, r, hr => by
    simp only [shelahHJDim]
    exact shelahCubeDim_pos _ (k + 1) r hr (shelahHJDim_pos (k + 1) r hr)

/-- Replace coordinate `j` of `w` with `v`. -/
def updateWord {m k : Nat} (w : Word m k) (j : Fin m) (v : Fin k) : Word m k :=
  fun i => if i = j then v else w i

/-- Concatenate `x : Word N k` and `y : Word D k` into `Word (N + D) k`. -/
def appendWord {N D k : Nat} (x : Word N k) (y : Word D k) : Word (N + D) k :=
  fun i => if h : i.val < N then x ⟨i.val, h⟩ else y ⟨i.val - N, by omega⟩

/-- Monotone boundary word `τ_s`: first `s` coordinates are `k`, remaining `N - s` are `0`. -/
def tauWord (N k : Nat) (_hk : k ≥ 1) (s : Fin (N + 1)) : Word N (k + 1) :=
  fun i => if i.val < s.val then ⟨k, Nat.lt_succ_self k⟩ else ⟨0, Nat.zero_lt_succ k⟩

/-- Shelah's Equal-Ends property: swapping letter `0` and letter `k` in any single
parameter coordinate `j` of subspace `S` leaves color `c` unchanged. -/
def EqualEnds {m D k r : Nat} (_hk : k ≥ 1) (S : CombSubspace m D (k + 1))
    (c : Word D (k + 1) → Fin r) : Prop :=
  ∀ (w : Word m (k + 1)) (j : Fin m),
    c (S.eval (updateWord w j ⟨0, Nat.zero_lt_succ k⟩)) =
    c (S.eval (updateWord w j ⟨k, Nat.lt_succ_self k⟩))

private def prefixWord (N k : Nat) (_hk : k ≥ 1) (a b : Fin (N + 1)) (t : Fin (k + 1)) :
    Word N (k + 1) :=
  fun i =>
    if i.val < a.val then ⟨k, Nat.lt_succ_self k⟩
    else if i.val < b.val then t
    else ⟨0, Nat.zero_lt_succ k⟩

private theorem prefixWord_zero (N k : Nat) (hk : k ≥ 1) (a b : Fin (N + 1)) :
    prefixWord N k hk a b ⟨0, Nat.zero_lt_succ k⟩ = tauWord N k hk a := by
  funext i
  by_cases ha : i.val < a.val
  · simp [prefixWord, tauWord, ha]
  · by_cases hb : i.val < b.val <;> simp [prefixWord, tauWord, ha, hb]

private theorem prefixWord_last (N k : Nat) (hk : k ≥ 1) (a b : Fin (N + 1)) (hab : a.val < b.val) :
    prefixWord N k hk a b ⟨k, Nat.lt_succ_self k⟩ = tauWord N k hk b := by
  funext i
  by_cases ha : i.val < a.val
  · have hb : i.val < b.val := Nat.lt_trans ha hab
    simp [prefixWord, tauWord, ha, hb]
  · by_cases hb : i.val < b.val <;> simp [prefixWord, tauWord, ha, hb]

private def tailWord {m k : Nat} (w : Word (m + 1) k) : Word m k :=
  fun j => w ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩

private def glueSubspace {N D' m k : Nat} (_hk : k ≥ 1) (a b : Fin (N + 1)) (hab : a.val < b.val)
    (S' : CombSubspace m D' (k + 1)) : CombSubspace (m + 1) (N + D') (k + 1) where
  coord := fun i =>
    if hi : i.val < N then
      if i.val < a.val then Sum.inl ⟨k, Nat.lt_succ_self k⟩
      else if i.val < b.val then Sum.inr ⟨0, Nat.zero_lt_succ m⟩
      else Sum.inl ⟨0, Nat.zero_lt_succ k⟩
    else
      match S'.coord ⟨i.val - N, by omega⟩ with
      | Sum.inl l => Sum.inl l
      | Sum.inr j => Sum.inr ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  surj := by
    intro ⟨jv, hjv⟩
    cases jv with
    | zero =>
      have haN : a.val < N := Nat.lt_of_lt_of_le hab (Nat.le_of_lt_succ b.isLt)
      refine ⟨⟨a.val, Nat.lt_of_lt_of_le haN (Nat.le_add_right N D')⟩, ?_⟩
      have hna : ¬ (a.val < a.val) := Nat.lt_irrefl _
      simp [haN, hna, hab]
    | succ jv' =>
      obtain ⟨i', hi'⟩ := S'.surj ⟨jv', Nat.lt_of_succ_lt_succ hjv⟩
      refine ⟨⟨N + i'.val, Nat.add_lt_add_left i'.isLt N⟩, ?_⟩
      have hnot : ¬ (N + i'.val < N) := by omega
      have hsub : (N + i'.val) - N = i'.val := Nat.add_sub_cancel_left N i'.val
      simp [hnot, hsub, hi']

private theorem glueSubspace_eval {N D' m k : Nat} (hk : k ≥ 1) (a b : Fin (N + 1))
    (hab : a.val < b.val) (S' : CombSubspace m D' (k + 1)) (w : Word (m + 1) (k + 1)) :
    (glueSubspace hk a b hab S').eval w =
      appendWord (prefixWord N k hk a b (w ⟨0, Nat.zero_lt_succ m⟩)) (S'.eval (tailWord w)) := by
  funext i
  by_cases hi : i.val < N
  · by_cases ha : i.val < a.val
    · simp [CombSubspace.eval, glueSubspace, appendWord, prefixWord, hi, ha]
    · by_cases hb : i.val < b.val <;>
        simp [CombSubspace.eval, glueSubspace, appendWord, prefixWord, hi, ha, hb]
  · simp only [CombSubspace.eval, glueSubspace, appendWord, tailWord, hi]
    cases hc : S'.coord ⟨i.val - N, by omega⟩ <;> simp [hc]

private theorem tailWord_update_zero {m k : Nat} (w : Word (m + 1) k) (v : Fin k) :
    tailWord (updateWord w ⟨0, Nat.zero_lt_succ m⟩ v) = tailWord w := by
  funext j
  simp [tailWord, updateWord]

private theorem tailWord_update_succ {m k : Nat} (w : Word (m + 1) k) (j' : Fin m) (v : Fin k) :
    tailWord (updateWord w ⟨j'.val + 1, Nat.succ_lt_succ j'.isLt⟩ v) =
      updateWord (tailWord w) j' v := by
  funext i
  by_cases hi : i = j'
  · subst hi
    simp [tailWord, updateWord]
  · have hne : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (m + 1)) ≠
        ⟨j'.val + 1, Nat.succ_lt_succ j'.isLt⟩ := by
      intro h
      apply hi
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp at hv
      omega
    simp [tailWord, updateWord, hi, hne]

/-- **Shelah's Cube Lemma**: for every `m, k ≥ 1, r ≥ 1`, any `r`-coloring of `[k+1]^{shelahCubeDim m k r}`
admits an `m`-dimensional combinatorial subspace satisfying the equal-ends invariance. -/
theorem shelah_equal_ends :
    ∀ (m k r : Nat) (hk : k ≥ 1) (_hr : r ≥ 1)
      (c : Word (shelahCubeDim m k r) (k + 1) → Fin r),
      ∃ S : CombSubspace m (shelahCubeDim m k r) (k + 1), EqualEnds hk S c
  | 0, _, _, _, _, _ =>
    ⟨{ coord := Fin.elim0, surj := fun j => j.elim0 }, fun _ j => j.elim0⟩
  | m + 1, k, r, hk, hr, c => by
    dsimp only [shelahCubeDim] at c ⊢
    let N := r ^ ((k + 1) ^ m)
    let R := r ^ ((k + 1) ^ N)
    let D' := shelahCubeDim m k R
    have hN : N ≥ 1 := pow_pos_of_pos r hr _
    have hR : R ≥ 1 := pow_pos_of_pos r hr _
    let ePrefix : FinEquiv (Word N (k + 1)) ((k + 1) ^ N) :=
      finEquivFun (finEquivFin (k + 1)) N
    let fullProfile : Word D' (k + 1) → Fin R :=
      fun y => encodeMap ePrefix (fun x => c (appendWord x y))
    obtain ⟨S', hS'⟩ := shelah_equal_ends m k R hk hR fullProfile
    have htailEq :
        ∀ (x : Word N (k + 1)) (w : Word m (k + 1)) (j : Fin m),
          c (appendWord x (S'.eval (updateWord w j ⟨0, Nat.zero_lt_succ k⟩))) =
          c (appendWord x (S'.eval (updateWord w j ⟨k, Nat.lt_succ_self k⟩))) := by
      intro x w j
      exact encodeMap_inj ePrefix (hS' w j) x
    let eWordM : FinEquiv (Word m (k + 1)) ((k + 1) ^ m) :=
      finEquivFun (finEquivFin (k + 1)) m
    let stepProfile : Fin (N + 1) → Fin N :=
      fun s => encodeMap eWordM (fun w => c (appendWord (tauWord N k hk s) (S'.eval w)))
    obtain ⟨a, b, hab, hstep⟩ := fin_pigeonhole N stepProfile
    have hfirstEq :
        ∀ (w : Word m (k + 1)),
          c (appendWord (tauWord N k hk a) (S'.eval w)) =
          c (appendWord (tauWord N k hk b) (S'.eval w)) := by
      intro w
      exact encodeMap_inj eWordM hstep w
    refine ⟨glueSubspace hk a b hab S', ?_⟩
    intro w ⟨jv, hjv⟩
    rw [glueSubspace_eval, glueSubspace_eval]
    cases jv with
    | zero =>
      have h0 : updateWord w ⟨0, hjv⟩ ⟨0, Nat.zero_lt_succ k⟩ ⟨0, Nat.zero_lt_succ m⟩ =
          ⟨0, Nat.zero_lt_succ k⟩ := by simp [updateWord]
      have hk' : updateWord w ⟨0, hjv⟩ ⟨k, Nat.lt_succ_self k⟩ ⟨0, Nat.zero_lt_succ m⟩ =
          ⟨k, Nat.lt_succ_self k⟩ := by simp [updateWord]
      rw [h0, hk', prefixWord_zero, prefixWord_last N k hk a b hab,
          tailWord_update_zero, tailWord_update_zero]
      exact hfirstEq (tailWord w)
    | succ jv' =>
      have h0 : updateWord w ⟨jv' + 1, hjv⟩ ⟨0, Nat.zero_lt_succ k⟩ ⟨0, Nat.zero_lt_succ m⟩ =
          w ⟨0, Nat.zero_lt_succ m⟩ := by simp [updateWord]
      have hk' : updateWord w ⟨jv' + 1, hjv⟩ ⟨k, Nat.lt_succ_self k⟩ ⟨0, Nat.zero_lt_succ m⟩ =
          w ⟨0, Nat.zero_lt_succ m⟩ := by simp [updateWord]
      have ht0 := tailWord_update_succ w ⟨jv', Nat.lt_of_succ_lt_succ hjv⟩ ⟨0, Nat.zero_lt_succ k⟩
      have htk := tailWord_update_succ w ⟨jv', Nat.lt_of_succ_lt_succ hjv⟩ ⟨k, Nat.lt_succ_self k⟩
      rw [h0, hk', ht0, htk]
      exact htailEq _ (tailWord w) ⟨jv', Nat.lt_of_succ_lt_succ hjv⟩

private def embedWord {m k : Nat} (w : Word m k) : Word m (k + 1) :=
  fun i => ⟨(w i).val, Nat.lt_succ_of_lt (w i).isLt⟩

private def liftLine {m k : Nat} (L : Line m k) : Line m (k + 1) where
  mask := fun i => (L.mask i).map (fun a => ⟨a.val, Nat.lt_succ_of_lt a.isLt⟩)
  hasWildcard := by
    obtain ⟨i, hi⟩ := L.hasWildcard
    refine ⟨i, ?_⟩
    simp [hi]

private theorem liftLine_eval_lt {m k : Nat} (L : Line m k) (t : Fin (k + 1)) (ht : t.val < k) :
    (liftLine L).eval t = embedWord (L.eval ⟨t.val, ht⟩) := by
  funext i
  cases hm : L.mask i with
  | none =>
    simp [Line.eval, evalMask, liftLine, embedWord, hm]
  | some a =>
    simp [Line.eval, evalMask, liftLine, embedWord, hm]

private def partialEnd {m k : Nat} (_hk : k ≥ 1) (L' : Line m (k + 1)) (n : Nat) :
    Word m (k + 1) :=
  fun i => match L'.mask i with
    | some a => a
    | none => if i.val < n then ⟨k, Nat.lt_succ_self k⟩ else ⟨0, Nat.zero_lt_succ k⟩

private theorem partialEnd_zero {m k : Nat} (hk : k ≥ 1) (L' : Line m (k + 1)) :
    partialEnd hk L' 0 = L'.eval ⟨0, Nat.zero_lt_succ k⟩ := by
  funext i
  cases hm : L'.mask i <;> simp [partialEnd, Line.eval, evalMask, hm]

private theorem partialEnd_full {m k : Nat} (hk : k ≥ 1) (L' : Line m (k + 1)) :
    partialEnd hk L' m = L'.eval ⟨k, Nat.lt_succ_self k⟩ := by
  funext i
  cases hm : L'.mask i <;> simp [partialEnd, Line.eval, evalMask, hm, i.isLt]

private theorem partialEnd_step {m D k r : Nat} (hk : k ≥ 1) (S : CombSubspace m D (k + 1))
    (c : Word D (k + 1) → Fin r) (heq : EqualEnds hk S c) (L' : Line m (k + 1)) :
    ∀ n : Nat, n ≤ m → c (S.eval (partialEnd hk L' 0)) = c (S.eval (partialEnd hk L' n))
  | 0, _ => rfl
  | n + 1, hn => by
    have ih := partialEnd_step hk S c heq L' n (Nat.le_of_lt hn)
    rw [ih]
    let idx : Fin m := ⟨n, hn⟩
    have hnot_lt : ¬ (idx.val < n) := Nat.lt_irrefl n
    have hlt_succ : idx.val < n + 1 := Nat.lt_succ_self n
    cases hm : L'.mask idx with
    | some a =>
      have hsame : partialEnd hk L' n = partialEnd hk L' (n + 1) := by
        funext i
        by_cases hi : i.val < n
        · have hi1 : i.val < n + 1 := Nat.lt_succ_of_lt hi
          cases hmi : L'.mask i <;> simp [partialEnd, hmi, hi, hi1]
        · by_cases hi1 : i.val < n + 1
          · have heq_i : i = idx := Fin.ext (by dsimp [idx]; omega)
            subst heq_i
            simp [partialEnd, hm]
          · cases hmi : L'.mask i <;> simp [partialEnd, hmi, hi, hi1]
      rw [hsame]
    | none =>
      have h0 : partialEnd hk L' n =
          updateWord (partialEnd hk L' n) idx ⟨0, Nat.zero_lt_succ k⟩ := by
        funext i
        by_cases hi : i = idx
        · subst hi
          simp [partialEnd, updateWord, hm, hnot_lt]
        · simp [updateWord, hi]
      have hk' : partialEnd hk L' (n + 1) =
          updateWord (partialEnd hk L' n) idx ⟨k, Nat.lt_succ_self k⟩ := by
        funext i
        by_cases hi : i = idx
        · subst hi
          simp [partialEnd, updateWord, hm, hlt_succ]
        · have hne : i.val ≠ n := fun h => hi (Fin.ext (by dsimp [idx]; exact h))
          have hiff : (i.val < n + 1) ↔ (i.val < n) := by omega
          cases hmi : L'.mask i <;> simp [partialEnd, updateWord, hi, hmi, hiff]
      rw [h0, hk']
      exact heq (partialEnd hk L' n) idx

/-- **Shelah's Explicit Primitive-Recursive Hales–Jewett Theorem**:
for every `k ≥ 1` and `r ≥ 1`, `HJUpper (shelahHJDim k r) k r` holds. -/
theorem hales_jewett_shelah :
    ∀ (k r : Nat), k ≥ 1 → r ≥ 1 → HJUpper (shelahHJDim k r) k r
  | 0, _, hk, _ => by omega
  | 1, r, _, hr => by
    simpa [shelahHJDim] using hj_alphabet_one r hr
  | k + 2, r, _, hr => by
    intro c
    have hk : k + 1 ≥ 1 := Nat.succ_pos k
    let m := shelahHJDim (k + 1) r
    change HasMonoLine (shelahCubeDim m (k + 1) r) (k + 2) r c
    obtain ⟨S, hS⟩ := shelah_equal_ends m (k + 1) r hk hr c
    have hIH : HJUpper m (k + 1) r := hales_jewett_shelah (k + 1) r hk hr
    let cTrunc : Word m (k + 1) → Fin r := fun w => c (S.eval (embedWord w))
    obtain ⟨L, color, hL⟩ := hIH cTrunc
    let L' : Line m (k + 2) := liftLine L
    refine ⟨S.pushLine L', color, ?_⟩
    intro t
    rw [S.pushLine_eval]
    by_cases ht : t.val < k + 1
    · rw [liftLine_eval_lt L t ht]
      exact hL ⟨t.val, ht⟩
    · have htlast : t = ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := Fin.ext (by dsimp; have := t.isLt; omega)
      have h0eq : c (S.eval (L'.eval ⟨0, Nat.zero_lt_succ (k + 1)⟩)) = color := by
        have hz : (⟨0, Nat.zero_lt_succ (k + 1)⟩ : Fin (k + 2)).val < k + 1 := hk
        rw [liftLine_eval_lt L ⟨0, Nat.zero_lt_succ (k + 1)⟩ hz]
        exact hL ⟨0, hz⟩
      have hends := partialEnd_step hk S c hS L' m (Nat.le_refl m)
      rw [partialEnd_zero, partialEnd_full] at hends
      rw [htlast, ← hends, h0eq]

/-- **Unconditional Hales–Jewett Theorem**: for any alphabet size `k ≥ 1` and color count `r ≥ 1`,
there exists a dimension `d ≥ 1` where every `r`-coloring of `[k]^d` has a monochromatic line. -/
theorem hales_jewett (k r : Nat) (hk : k ≥ 1) (hr : r ≥ 1) :
    ∃ d : Nat, d ≥ 1 ∧ HJUpper d k r :=
  ⟨shelahHJDim k r, shelahHJDim_pos k r hr, hales_jewett_shelah k r hk hr⟩

/-- **Unconditional Van der Waerden Theorem**: for any progression length `k ≥ 1` and color count
`r ≥ 1`, there exists `N ≥ 1` where every `r`-coloring of `{0, ..., N - 1}` has a monochromatic `k`-AP. -/
theorem van_der_waerden (k r : Nat) (hk : k ≥ 1) (hr : r ≥ 1) :
    ∃ N : Nat, N ≥ 1 ∧ HasMonoAP N k r := by
  cases k with
  | zero => omega
  | succ k' =>
    have hhj := hales_jewett_shelah (k' + 1) r hk hr
    exact ⟨shelahHJDim (k' + 1) r * k' + 1, Nat.succ_pos _, hj_implies_vdw hhj⟩

end HJBrigade
