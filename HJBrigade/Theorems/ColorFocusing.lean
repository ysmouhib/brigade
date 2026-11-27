import HJBrigade.Core.Line

/-!
# Combinatorial Subspaces and Color-Focusing Machinery

Provides the reusable combinatorial infrastructure behind Shelah's / Hales–Jewett's
inductive proofs:
1. `CombSubspace m d k`: an `m`-dimensional combinatorial subspace inside `[k]^d`,
   with `pushLine` and `pullback_hj`.
2. `ColorFocusedLines s d k`: a star of `s` combinatorial lines meeting at a common
   focus word on letter `k - 1`, together with `color_focused_dichotomy`.
-/

namespace HJBrigade

/-- An `m`-dimensional combinatorial subspace of `[k]^d` whose coordinates are either
fixed constants `Sum.inl a` or bound to one of `m` parameter slots `Sum.inr j`,
with every parameter slot realized at least once. -/
structure CombSubspace (m d k : Nat) where
  coord : Fin d → Sum (Fin k) (Fin m)
  surj : ∀ j : Fin m, ∃ i : Fin d, coord i = Sum.inr j

def CombSubspace.eval {m d k : Nat} (S : CombSubspace m d k) (w : Word m k) : Word d k :=
  fun i => match S.coord i with
    | Sum.inl a => a
    | Sum.inr j => w j

theorem CombSubspace.eval_injective {m d k : Nat} (S : CombSubspace m d k)
    {w₁ w₂ : Word m k} (h : S.eval w₁ = S.eval w₂) : w₁ = w₂ := by
  funext j
  obtain ⟨i, hi⟩ := S.surj j
  have hpt := congrFun h i
  simpa [CombSubspace.eval, hi] using hpt

def CombSubspace.pushLine {m d k : Nat} (S : CombSubspace m d k) (L : Line m k) : Line d k where
  mask := fun i => match S.coord i with
    | Sum.inl a => some a
    | Sum.inr j => L.mask j
  hasWildcard := by
    obtain ⟨j, hj⟩ := L.hasWildcard
    obtain ⟨i, hi⟩ := S.surj j
    refine ⟨i, ?_⟩
    simp [hi, hj]

theorem CombSubspace.pushLine_eval {m d k : Nat} (S : CombSubspace m d k) (L : Line m k) (t : Fin k) :
    (S.pushLine L).eval t = S.eval (L.eval t) := by
  funext i
  cases h : S.coord i <;> simp [Line.eval, evalMask, CombSubspace.pushLine, CombSubspace.eval, h]

/-- If `[k]^m` satisfies `HJUpper m k r`, then any `[k]^d` containing an `m`-dimensional
combinatorial subspace also satisfies `HJUpper d k r`. -/
theorem CombSubspace.pullback_hj {m d k r : Nat} (S : CombSubspace m d k) (h : HJUpper m k r) :
    HJUpper d k r := by
  intro c
  obtain ⟨L, color, hL⟩ := h (fun w => c (S.eval w))
  refine ⟨S.pushLine L, color, ?_⟩
  intro t
  rw [S.pushLine_eval]
  exact hL t

/-- A color-focused family of `s` combinatorial lines in `[k]^d` whose final points
(at letter `k - 1`) all coincide at `focus`. -/
structure ColorFocusedLines (s d k : Nat) (hk : k ≥ 2) where
  focus : Word d k
  lines : Fin s → Line d k
  at_last : ∀ j : Fin s, (lines j).eval ⟨k - 1, by omega⟩ = focus

/-- Every injection `Fin r → Fin r` is surjective (proved constructively via `fin_pigeonhole`). -/
theorem fin_inj_surj {r : Nat} (f : Fin r → Fin r)
    (hinj : ∀ a b : Fin r, f a = f b → a = b) (y : Fin r) : ∃ j : Fin r, f j = y := by
  let g : Fin (r + 1) → Fin r := fun ⟨v, hv⟩ =>
    if h : v < r then f ⟨v, h⟩ else y
  obtain ⟨a, b, hab, hgab⟩ := fin_pigeonhole r g
  have hlt_a : a.val < r := Nat.lt_of_lt_of_le hab (Nat.le_of_lt_succ b.isLt)
  by_cases hb : b.val < r
  · have hfa : g a = f ⟨a.val, hlt_a⟩ := by simp [g, hlt_a]
    have hfb : g b = f ⟨b.val, hb⟩ := by simp [g, hb]
    have heq := hinj ⟨a.val, hlt_a⟩ ⟨b.val, hb⟩ (hfa.symm.trans (hgab.trans hfb))
    have hval := congrArg Fin.val heq
    exact absurd hval (Nat.ne_of_lt hab)
  · have hfa : g a = f ⟨a.val, hlt_a⟩ := by simp [g, hlt_a]
    have hfb : g b = y := by simp [g, hb]
    exact ⟨⟨a.val, hlt_a⟩, hfa.symm.trans (hgab.trans hfb)⟩

/-- Color-focusing dichotomy: if `r` lines in `[k]^d` share a common endpoint at `k - 1`
and their truncated `(k - 1)`-prefixes are monochromatic in `r` pairwise distinct colors,
then one of the `r` lines is fully monochromatic. -/
theorem color_focused_dichotomy {d k r : Nat} (hk : k ≥ 2)
    (F : ColorFocusedLines r d k hk) (c : Word d k → Fin r)
    (lineColor : Fin r → Fin r)
    (hpref : ∀ (j : Fin r) (t : Fin k), t.val < k - 1 → c ((F.lines j).eval t) = lineColor j)
    (hdist : ∀ j₁ j₂ : Fin r, lineColor j₁ = lineColor j₂ → j₁ = j₂) :
    HasMonoLine d k r c := by
  obtain ⟨j, hj⟩ := fin_inj_surj lineColor hdist (c F.focus)
  refine ⟨F.lines j, c F.focus, ?_⟩
  intro t
  by_cases ht : t.val < k - 1
  · rw [hpref j t ht, hj]
  · have htlast : t = ⟨k - 1, by omega⟩ := Fin.ext (by dsimp; have := t.isLt; omega)
    rw [htlast, F.at_last j]

end HJBrigade
