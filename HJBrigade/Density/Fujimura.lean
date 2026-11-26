import HJBrigade.Density.Sperner

/-!
# Fujimura's Simplex-Free Reduction (`Word d 3 → Bool`)

Permutation-invariant (`S_d`) subsets `fujimuraSet d T` depend only on the letter counts
`(n₀, n₁, n₂)` of a word in `[3]^d`. Combinatorial lines correspond to equilateral
triangles `(a + r, b, c)`, `(a, b + r, c)`, `(a, b, c + r)` (`r ≥ 1, a + b + c + r = d`),
enabling fast kernel-checked lower bounds for `[3]^5`, `[3]^6`, and higher dimensions.

Includes Polymath-1 / Fujimura lower bounds:
- `c_5_3_ge_150` (`[3]^5`)
- `c_6_3_ge_450` (`[3]^6`)
-/

namespace HJBrigade

/-- Count occurrences of letter `a : Fin 3` in a word `w : Word d 3`. -/
def letterCount : ∀ {d : Nat}, Fin 3 → Word d 3 → Nat
  | 0, _, _ => 0
  | _ + 1, a, w =>
    (if w ⟨0, Nat.zero_lt_succ _⟩ = a then 1 else 0) +
      letterCount a (fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-- Symmetric (`S_d`-invariant) subset of `[3]^d` determined by letter-count predicate `T`. -/
def fujimuraSet (d : Nat) (T : Nat → Nat → Nat → Bool) (w : Word d 3) : Bool :=
  T (letterCount ⟨0, by decide⟩ w) (letterCount ⟨1, by decide⟩ w) (letterCount ⟨2, by decide⟩ w)

/-- Exact closed-form recurrence computing `wordCard (fujimuraSet d T)` in `O(3^d)` arithmetic ops. -/
def fujimuraCard : Nat → (Nat → Nat → Nat → Bool) → Nat
  | 0, T => if T 0 0 0 then 1 else 0
  | d + 1, T =>
    fujimuraCard d (fun a b c => T (a + 1) b c) +
    fujimuraCard d (fun a b c => T a (b + 1) c) +
    fujimuraCard d (fun a b c => T a b (c + 1))

private theorem fujimuraSet_cons0 (d : Nat) (T : Nat → Nat → Nat → Bool) (w : Word d 3) :
    fujimuraSet (d + 1) T (consFin ⟨0, by decide⟩ w) =
      fujimuraSet d (fun a b c => T (a + 1) b c) w := by
  dsimp only [fujimuraSet, letterCount, consFin]
  simp [Nat.add_comm]

private theorem fujimuraSet_cons1 (d : Nat) (T : Nat → Nat → Nat → Bool) (w : Word d 3) :
    fujimuraSet (d + 1) T (consFin ⟨1, by decide⟩ w) =
      fujimuraSet d (fun a b c => T a (b + 1) c) w := by
  dsimp only [fujimuraSet, letterCount, consFin]
  simp [Nat.add_comm]

private theorem fujimuraSet_cons2 (d : Nat) (T : Nat → Nat → Nat → Bool) (w : Word d 3) :
    fujimuraSet (d + 1) T (consFin ⟨2, by decide⟩ w) =
      fujimuraSet d (fun a b c => T a b (c + 1)) w := by
  dsimp only [fujimuraSet, letterCount, consFin]
  simp [Nat.add_comm]

theorem wordCard_fujimuraSet :
    ∀ (d : Nat) (T : Nat → Nat → Nat → Bool), wordCard (fujimuraSet d T) = fujimuraCard d T
  | 0, T => rfl
  | d + 1, T => by
    simp only [wordCard, sumFin, fujimuraCard]
    have h0 : (fun w : Word d 3 => fujimuraSet (d + 1) T (consFin ⟨0, Nat.zero_lt_succ 2⟩ w)) =
        fujimuraSet d (fun a b c => T (a + 1) b c) := funext (fujimuraSet_cons0 d T)
    have h1 : (fun w : Word d 3 => fujimuraSet (d + 1) T (consFin ⟨1, by decide⟩ w)) =
        fujimuraSet d (fun a b c => T a (b + 1) c) := funext (fujimuraSet_cons1 d T)
    have h2 : (fun w : Word d 3 => fujimuraSet (d + 1) T (consFin ⟨2, by decide⟩ w)) =
        fujimuraSet d (fun a b c => T a b (c + 1)) := funext (fujimuraSet_cons2 d T)
    have ih0 := wordCard_fujimuraSet d (fun a b c => T (a + 1) b c)
    have ih1 := wordCard_fujimuraSet d (fun a b c => T a (b + 1) c)
    have ih2 := wordCard_fujimuraSet d (fun a b c => T a b (c + 1))
    rw [h0, h1, h2, ih0, ih1, ih2]
    omega

private def countMaskConst : ∀ {d : Nat}, Fin 3 → (Fin d → Option (Fin 3)) → Nat
  | 0, _, _ => 0
  | _ + 1, a, mask =>
    (if mask ⟨0, Nat.zero_lt_succ _⟩ = some a then 1 else 0) +
      countMaskConst a (fun i => mask ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private def countMaskWild : ∀ {d : Nat}, (Fin d → Option (Fin 3)) → Nat
  | 0, _ => 0
  | _ + 1, mask =>
    (if mask ⟨0, Nat.zero_lt_succ _⟩ = none then 1 else 0) +
      countMaskWild (fun i => mask ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private theorem countMask_sum :
    ∀ {d : Nat} (mask : Fin d → Option (Fin 3)),
      countMaskConst ⟨0, by decide⟩ mask +
      countMaskConst ⟨1, by decide⟩ mask +
      countMaskConst ⟨2, by decide⟩ mask +
      countMaskWild mask = d
  | 0, _ => rfl
  | d + 1, mask => by
    have ih := countMask_sum (fun i : Fin d => mask ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    dsimp only [countMaskConst, countMaskWild]
    cases hm : mask ⟨0, Nat.zero_lt_succ d⟩ with
    | none =>
      simp only [reduceCtorEq, ↓reduceIte]
      omega
    | some x =>
      have hx := x.isLt
      match hxv : x.val with
      | 0 =>
        have hx0 : x = ⟨0, by decide⟩ := Fin.ext hxv
        subst hx0
        simp at ih ⊢
        omega
      | 1 =>
        have hx1 : x = ⟨1, by decide⟩ := Fin.ext hxv
        subst hx1
        simp at ih ⊢
        omega
      | 2 =>
        have hx2 : x = ⟨2, by decide⟩ := Fin.ext hxv
        subst hx2
        simp at ih ⊢
        omega
      | _ + 3 => omega

private theorem countMaskWild_pos :
    ∀ {d : Nat} (mask : Fin d → Option (Fin 3)),
      (∃ i : Fin d, mask i = none) → 1 ≤ countMaskWild mask
  | 0, _, ⟨i, _⟩ => i.elim0
  | d + 1, mask, ⟨⟨v, hv⟩, hnone⟩ => by
    dsimp only [countMaskWild]
    cases v with
    | zero =>
      simp only [hnone, ↓reduceIte]
      omega
    | succ v' =>
      have ih := countMaskWild_pos (fun i : Fin d => mask ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        ⟨⟨v', Nat.lt_of_succ_lt_succ hv⟩, hnone⟩
      omega

private theorem letterCount_evalMask_eq :
    ∀ {d : Nat} (a t : Fin 3) (mask : Fin d → Option (Fin 3)),
      letterCount a (evalMask mask t) =
        countMaskConst a mask + (if t = a then countMaskWild mask else 0)
  | 0, _, _, _ => by simp [letterCount, countMaskConst, countMaskWild]
  | d + 1, a, t, mask => by
    have ih := letterCount_evalMask_eq a t (fun i : Fin d => mask ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    dsimp only [letterCount, countMaskConst, countMaskWild, evalMask]
    change (if (mask ⟨0, Nat.zero_lt_succ d⟩).getD t = a then 1 else 0) +
      letterCount a (evalMask (fun i : Fin d => mask ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) t) = _
    rw [ih]
    cases mask ⟨0, Nat.zero_lt_succ d⟩ with
    | none =>
      simp only [Option.getD_none, reduceCtorEq, ↓reduceIte]
      by_cases ht : t = a <;> simp [ht] <;> omega
    | some x =>
      simp only [Option.getD_some, Option.some.injEq, reduceCtorEq, ↓reduceIte]
      by_cases hx : x = a <;> by_cases ht : t = a <;> simp [hx, ht] <;> omega

/-- Check over the Fujimura simplex grid that `T` contains no equilateral triangle `(a+r,b,c), (a,b+r,c), (a,b,c+r)`. -/
def checkSimplexFree (d : Nat) (T : Nat → Nat → Nat → Bool) : Bool :=
  decide (∀ a : Fin (d + 1), ∀ b : Fin (d + 1), ∀ c : Fin (d + 1),
    a.val + b.val + c.val < d →
      let r := d - (a.val + b.val + c.val)
      !(T (a.val + r) b.val c.val && T a.val (b.val + r) c.val && T a.val b.val (c.val + r)))

theorem fujimura_isLineFree (d : Nat) (T : Nat → Nat → Nat → Bool)
    (hT : checkSimplexFree d T = true) : IsLineFree (fujimuraSet d T) := by
  intro L
  have hall := of_decide_eq_true hT
  let a := countMaskConst ⟨0, by decide⟩ L.mask
  let b := countMaskConst ⟨1, by decide⟩ L.mask
  let c := countMaskConst ⟨2, by decide⟩ L.mask
  let r := countMaskWild L.mask
  have hsum : a + b + c + r = d := countMask_sum L.mask
  have hrpos : 1 ≤ r := countMaskWild_pos L.mask L.hasWildcard
  have hlt : a + b + c < d := by omega
  have hnot := hall ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ hlt
  have hreq : d - (a + b + c) = r := by omega
  dsimp only at hnot
  rw [hreq] at hnot
  by_cases h0 : fujimuraSet d T (L.eval ⟨0, by decide⟩) = false
  · exact ⟨⟨0, by decide⟩, h0⟩
  · by_cases h1 : fujimuraSet d T (L.eval ⟨1, by decide⟩) = false
    · exact ⟨⟨1, by decide⟩, h1⟩
    · refine ⟨⟨2, by decide⟩, ?_⟩
      cases h2 : fujimuraSet d T (L.eval ⟨2, by decide⟩) with
      | false => rfl
      | true =>
        exfalso
        have ht0 : fujimuraSet d T (L.eval ⟨0, by decide⟩) = true := by
          cases h : fujimuraSet d T (L.eval ⟨0, by decide⟩) <;> simp_all
        have ht1 : fujimuraSet d T (L.eval ⟨1, by decide⟩) = true := by
          cases h : fujimuraSet d T (L.eval ⟨1, by decide⟩) <;> simp_all
        have ht2 : fujimuraSet d T (L.eval ⟨2, by decide⟩) = true := h2
        dsimp only [fujimuraSet, Line.eval] at ht0 ht1 ht2
        rw [letterCount_evalMask_eq ⟨0, by decide⟩ ⟨0, by decide⟩ L.mask,
            letterCount_evalMask_eq ⟨1, by decide⟩ ⟨0, by decide⟩ L.mask,
            letterCount_evalMask_eq ⟨2, by decide⟩ ⟨0, by decide⟩ L.mask] at ht0
        rw [letterCount_evalMask_eq ⟨0, by decide⟩ ⟨1, by decide⟩ L.mask,
            letterCount_evalMask_eq ⟨1, by decide⟩ ⟨1, by decide⟩ L.mask,
            letterCount_evalMask_eq ⟨2, by decide⟩ ⟨1, by decide⟩ L.mask] at ht1
        rw [letterCount_evalMask_eq ⟨0, by decide⟩ ⟨2, by decide⟩ L.mask,
            letterCount_evalMask_eq ⟨1, by decide⟩ ⟨2, by decide⟩ L.mask,
            letterCount_evalMask_eq ⟨2, by decide⟩ ⟨2, by decide⟩ L.mask] at ht2
        have hp0 : T (a + r) b c = true := by simpa [a, b, c, r] using ht0
        have hp1 : T a (b + r) c = true := by simpa [a, b, c, r] using ht1
        have hp2 : T a b (c + r) = true := by simpa [a, b, c, r] using ht2
        rw [hp0, hp1, hp2] at hnot
        simp at hnot

/-- Build a count-profile predicate from an explicit list of allowed `(n₀, n₁, n₂)` triples. -/
def triplePred (triples : List (Nat × Nat × Nat)) (a b c : Nat) : Bool :=
  triples.contains (a, b, c)

theorem fujimura_lower_bound (d size : Nat) (triples : List (Nat × Nat × Nat))
    (hFree : checkSimplexFree d (triplePred triples) = true)
    (hCard : fujimuraCard d (triplePred triples) = size) :
    ∃ A : Word d 3 → Bool, IsLineFree A ∧ wordCard A = size := by
  refine ⟨fujimuraSet d (triplePred triples), fujimura_isLineFree d _ hFree, ?_⟩
  rw [wordCard_fujimuraSet, hCard]

private def polymath_d5_triples : List (Nat × Nat × Nat) :=
  [(0, 1, 4), (0, 2, 3), (1, 0, 4), (1, 2, 2), (1, 3, 1),
   (2, 0, 3), (2, 1, 2), (2, 3, 0), (3, 1, 1), (3, 2, 0)]

/-- Exact Polymath-1 lower bound `c_{5, 3} ≥ 150` via Fujimura simplex-free construction. -/
theorem c_5_3_ge_150 : ∃ A : Word 5 3 → Bool, IsLineFree A ∧ wordCard A = 150 :=
  fujimura_lower_bound 5 150 polymath_d5_triples (by decide) (by decide)

private def polymath_d6_triples : List (Nat × Nat × Nat) :=
  [(1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1),
   (0, 2, 4), (0, 4, 2), (2, 0, 4), (2, 4, 0), (4, 0, 2), (4, 2, 0)]

/-- Exact Polymath-1 lower bound `c_{6, 3} ≥ 450` via Fujimura simplex-free construction. -/
theorem c_6_3_ge_450 : ∃ A : Word 6 3 → Bool, IsLineFree A ∧ wordCard A = 450 :=
  fujimura_lower_bound 6 450 polymath_d6_triples (by decide) (by decide)

end HJBrigade
