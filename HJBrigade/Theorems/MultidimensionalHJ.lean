import HJBrigade.Theorems.Shelah

/-!
# Multidimensional Hales–Jewett Theorem

Formalizes `m`-dimensional combinatorial subspaces `IsMonoSubspace`, `MHJUpper m D k r`,
the equivalence `mhj_one_iff_hj`, explicit primitive-recursive dimension bound `mhjDim m k r`,
and the full unconditional **`multidimensional_hales_jewett`** theorem via Shelah's
Hales–Jewett theorem (`hales_jewett_shelah`) and product coloring profiles.
-/

namespace HJBrigade

private theorem pow_pos_mhj (r : Nat) (hr : r ≥ 1) : ∀ n : Nat, r ^ n ≥ 1
  | 0 => by simp
  | n + 1 => by
    have ih := pow_pos_mhj r hr n
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih hr

/-- A combinatorial subspace `S` is monochromatic under `c` if all words in `S` share one color. -/
def IsMonoSubspace {m D k r : Nat} (c : Word D k → Fin r) (S : CombSubspace m D k) : Prop :=
  ∃ color : Fin r, ∀ w : Word m k, c (S.eval w) = color

/-- `MHJUpper m D k r` asserts that every `r`-coloring of `[k]^D` admits a monochromatic
`m`-dimensional combinatorial subspace. -/
def MHJUpper (m D k r : Nat) : Prop :=
  ∀ c : Word D k → Fin r, ∃ S : CombSubspace m D k, IsMonoSubspace c S

private def lineToSubspace {D k : Nat} (L : Line D k) : CombSubspace 1 D k where
  coord := fun i => match L.mask i with
    | some a => Sum.inl a
    | none => Sum.inr ⟨0, Nat.zero_lt_succ 0⟩
  surj := fun ⟨v, hv⟩ => by
    have hv0 : v = 0 := by omega
    subst hv0
    obtain ⟨i, hi⟩ := L.hasWildcard
    refine ⟨i, ?_⟩
    simp [hi]

private theorem lineToSubspace_eval {D k : Nat} (L : Line D k) (w : Word 1 k) :
    (lineToSubspace L).eval w = L.eval (w ⟨0, Nat.zero_lt_succ 0⟩) := by
  funext i
  cases hm : L.mask i <;> simp [CombSubspace.eval, lineToSubspace, Line.eval, evalMask, hm]

private def subspaceToLine {D k : Nat} (S : CombSubspace 1 D k) : Line D k where
  mask := fun i => match S.coord i with
    | Sum.inl a => some a
    | Sum.inr _ => none
  hasWildcard := by
    obtain ⟨i, hi⟩ := S.surj ⟨0, Nat.zero_lt_succ 0⟩
    refine ⟨i, ?_⟩
    simp [hi]

private theorem subspaceToLine_eval {D k : Nat} (S : CombSubspace 1 D k) (t : Fin k) :
    (subspaceToLine S).eval t = S.eval (fun _ => t) := by
  funext i
  cases hc : S.coord i <;> simp [Line.eval, evalMask, subspaceToLine, CombSubspace.eval, hc]

/-- 1-dimensional Multidimensional Hales–Jewett coincides with ordinary `HJUpper`. -/
theorem mhj_one_iff_hj (D k r : Nat) : MHJUpper 1 D k r ↔ HJUpper D k r := by
  constructor
  · intro h c
    obtain ⟨S, col, hS⟩ := h c
    refine ⟨subspaceToLine S, col, ?_⟩
    intro t
    rw [subspaceToLine_eval]
    exact hS (fun _ => t)
  · intro h c
    obtain ⟨L, col, hL⟩ := h c
    refine ⟨lineToSubspace L, col, ?_⟩
    intro w
    rw [lineToSubspace_eval]
    exact hL (w ⟨0, Nat.zero_lt_succ 0⟩)

/-- Explicit primitive-recursive dimension bound for `m`-dimensional Hales–Jewett. -/
def mhjDim : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | m + 1, k, r =>
    let d1 := shelahHJDim k r
    let R := r ^ (k ^ d1)
    d1 + mhjDim m k R

theorem mhjDim_pos : ∀ (m k r : Nat), m ≥ 1 → r ≥ 1 → mhjDim m k r ≥ 1
  | 0, _, _, hm, _ => by omega
  | m + 1, k, r, _, hr => by
    simp only [mhjDim]
    have hd1 := shelahHJDim_pos k r hr
    omega

private def prodLineSubspace {m d1 d2 k : Nat} (L1 : Line d1 k) (S2 : CombSubspace m d2 k) :
    CombSubspace (m + 1) (d1 + d2) k where
  coord := fun i =>
    if hi : i.val < d1 then
      match L1.mask ⟨i.val, hi⟩ with
      | some a => Sum.inl a
      | none => Sum.inr ⟨0, Nat.zero_lt_succ m⟩
    else
      match S2.coord ⟨i.val - d1, by omega⟩ with
      | Sum.inl a => Sum.inl a
      | Sum.inr j => Sum.inr ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  surj := by
    intro ⟨jv, hjv⟩
    cases jv with
    | zero =>
      obtain ⟨i1, hi1⟩ := L1.hasWildcard
      refine ⟨⟨i1.val, Nat.lt_of_lt_of_le i1.isLt (Nat.le_add_right d1 d2)⟩, ?_⟩
      simp [i1.isLt, hi1]
    | succ jv' =>
      obtain ⟨i2, hi2⟩ := S2.surj ⟨jv', Nat.lt_of_succ_lt_succ hjv⟩
      refine ⟨⟨d1 + i2.val, Nat.add_lt_add_left i2.isLt d1⟩, ?_⟩
      have hnot : ¬ (d1 + i2.val < d1) := by omega
      have hsub : (d1 + i2.val) - d1 = i2.val := Nat.add_sub_cancel_left d1 i2.val
      simp [hnot, hsub, hi2]

private theorem prodLineSubspace_eval {m d1 d2 k : Nat}
    (L1 : Line d1 k) (S2 : CombSubspace m d2 k) (w : Word (m + 1) k) :
    (prodLineSubspace L1 S2).eval w =
      appendWord (L1.eval (w ⟨0, Nat.zero_lt_succ m⟩))
        (S2.eval (fun j => w ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)) := by
  funext i
  by_cases hi : i.val < d1
  · simp only [CombSubspace.eval, prodLineSubspace, appendWord, hi, Line.eval, evalMask]
    cases hm : L1.mask ⟨i.val, hi⟩ <;> simp [hm]
  · simp only [CombSubspace.eval, prodLineSubspace, appendWord, hi]
    cases hc : S2.coord ⟨i.val - d1, by omega⟩ <;> simp [hc]

/-- **Multidimensional Hales–Jewett Theorem (Explicit Bound)**: for all `m`, `k ≥ 1`, `r ≥ 1`,
every `r`-coloring of `[k]^{mhjDim m k r}` contains a monochromatic `m`-dimensional subspace. -/
theorem mhj_shelah :
    ∀ (m k r : Nat), k ≥ 1 → r ≥ 1 → MHJUpper m (mhjDim m k r) k r
  | 0, k, _, _, _, c => by
    dsimp only [mhjDim] at c ⊢
    refine ⟨⟨Fin.elim0, fun j => j.elim0⟩, c Fin.elim0, ?_⟩
    intro w
    have heval : ({ coord := Fin.elim0, surj := fun j => j.elim0 } : CombSubspace 0 0 k).eval w = Fin.elim0 :=
      (elim0_eta _).symm
    rw [heval]
  | m + 1, k, r, hk, hr, c => by
    dsimp only [mhjDim] at c ⊢
    let d1 := shelahHJDim k r
    let R := r ^ (k ^ d1)
    let d2 := mhjDim m k R
    have hk_pow : k ^ d1 ≥ 1 := pow_pos_mhj k hk d1
    have hR : R ≥ 1 := pow_pos_mhj r hr (k ^ d1)
    let e1 : FinEquiv (Word d1 k) (k ^ d1) := finEquivFun (finEquivFin k) d1
    let profile : Word d2 k → Fin R :=
      fun y => encodeMap e1 (fun x => c (appendWord x y))
    obtain ⟨S2, _, hS2⟩ := mhj_shelah m k R hk hR profile
    let w0 : Word m k := fun _ => ⟨0, hk⟩
    let c0 : Word d1 k → Fin r := fun x => c (appendWord x (S2.eval w0))
    have hc_eq : ∀ (x : Word d1 k) (w : Word m k),
        c (appendWord x (S2.eval w)) = c0 x :=
      fun x w => encodeMap_inj e1 ((hS2 w).trans (hS2 w0).symm) x
    obtain ⟨L1, col, hL1⟩ := hales_jewett_shelah k r hk hr c0
    refine ⟨prodLineSubspace L1 S2, col, ?_⟩
    intro w
    rw [prodLineSubspace_eval, hc_eq]
    exact hL1 (w ⟨0, Nat.zero_lt_succ m⟩)

/-- **Unconditional Multidimensional Hales–Jewett Theorem**: for every `m ≥ 1, k ≥ 1, r ≥ 1`,
there exists `D ≥ 1` such that every `r`-coloring of `[k]^D` contains a monochromatic `m`-subspace. -/
theorem multidimensional_hales_jewett (m k r : Nat) (hm : m ≥ 1) (hk : k ≥ 1) (hr : r ≥ 1) :
    ∃ D : Nat, D ≥ 1 ∧ MHJUpper m D k r :=
  ⟨mhjDim m k r, mhjDim_pos m k r hm hr, mhj_shelah m k r hk hr⟩

end HJBrigade
