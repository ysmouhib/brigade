import HJBrigade.Density.Slice9
import HJBrigade.Density.Fujimura
import HJBrigade.Density.ExactDHJ

/-!
# Geometric Lines and Moser Numbers (`c'_{d, 3}`) in `[3]^d`

Formalizes geometric lines (allowing both `+1` and `-1` coordinate directions in `[3]^d`),
monotonicity `isGeomLineFree_implies_isLineFree`, slice submultiplicativity `geomLineFree_slice_bound`,
and exact / improved Moser numbers verified purely in Lean 4's kernel:
- `moser_1_3_exact`: `c'_{1, 3} = 2`
- `moser_2_3_exact`: `c'_{2, 3} = 6`
- `moser_3_3_exact`: `c'_{3, 3} = 16` (`moser_3_3_strict_gap` vs `c_{3, 3} = 18`)
- `moser_4_3_upper_48`: `c'_{4, 3} ≤ 48`
- `moser_4_3_ge_43`: explicit `S_4`-invariant 43-point witness (`c'_{4, 3} ≥ 43`)
-/

namespace HJBrigade

/-- Coordinate behavior along a geometric line in `[3]^d`: constant `a`, forward `t`, or reversed `2 - t`. -/
inductive GeomMode where
  | const : Fin 3 → GeomMode
  | pos : GeomMode
  | neg : GeomMode
  deriving DecidableEq

instance : FinDomain GeomMode where
  decForall := fun P _ =>
    if h0 : P (.const ⟨0, by decide⟩) then
      if h1 : P (.const ⟨1, by decide⟩) then
        if h2 : P (.const ⟨2, by decide⟩) then
          if h3 : P .pos then
            if h4 : P .neg then
              isTrue fun m => match m with
                | .const ⟨0, _⟩ => h0
                | .const ⟨1, _⟩ => h1
                | .const ⟨2, _⟩ => h2
                | .const ⟨_ + 3, hi⟩ => absurd hi (by omega)
                | .pos => h3
                | .neg => h4
            else isFalse fun h => h4 (h .neg)
          else isFalse fun h => h3 (h .pos)
        else isFalse fun h => h2 (h (.const ⟨2, by decide⟩))
      else isFalse fun h => h1 (h (.const ⟨1, by decide⟩))
    else isFalse fun h => h0 (h (.const ⟨0, by decide⟩))
  decExists := fun P _ =>
    if h0 : P (.const ⟨0, by decide⟩) then isTrue ⟨.const ⟨0, by decide⟩, h0⟩
    else if h1 : P (.const ⟨1, by decide⟩) then isTrue ⟨.const ⟨1, by decide⟩, h1⟩
    else if h2 : P (.const ⟨2, by decide⟩) then isTrue ⟨.const ⟨2, by decide⟩, h2⟩
    else if h3 : P .pos then isTrue ⟨.pos, h3⟩
    else if h4 : P .neg then isTrue ⟨.neg, h4⟩
    else isFalse fun ⟨m, hm⟩ => match m, hm with
      | .const ⟨0, _⟩, h => h0 h
      | .const ⟨1, _⟩, h => h1 h
      | .const ⟨2, _⟩, h => h2 h
      | .const ⟨_ + 3, hi⟩, _ => absurd hi (by omega)
      | .pos, h => h3 h
      | .neg, h => h4 h

def negFin3 (t : Fin 3) : Fin 3 :=
  ⟨2 - t.val, by have := t.isLt; omega⟩

def evalGeomMode (m : GeomMode) (t : Fin 3) : Fin 3 :=
  match m with
  | .const a => a
  | .pos => t
  | .neg => negFin3 t

def evalGeomMask {d : Nat} (mode : Fin d → GeomMode) (t : Fin 3) : Word d 3 :=
  fun i => evalGeomMode (mode i) t

/-- A geometric line in `[3]^d` has at least one moving (`+1` or `-1`) coordinate. -/
structure GeomLine (d : Nat) where
  mode : Fin d → GeomMode
  hasActive : ∃ i : Fin d, mode i = .pos ∨ mode i = .neg

def GeomLine.eval {d : Nat} (L : GeomLine d) (t : Fin 3) : Word d 3 :=
  evalGeomMask L.mode t

/-- `IsGeomLineFree A` holds iff every geometric line in `[3]^d` hits a point outside `A`. -/
def IsGeomLineFree {d : Nat} (A : Word d 3 → Bool) : Prop :=
  ∀ L : GeomLine d, ∃ t : Fin 3, A (L.eval t) = false

theorem isGeomLineFree_iff_mode {d : Nat} (A : Word d 3 → Bool) :
    IsGeomLineFree A ↔
      ∀ mode : Fin d → GeomMode, (∃ i : Fin d, mode i = .pos ∨ mode i = .neg) →
        ∃ t : Fin 3, A (evalGeomMask mode t) = false := by
  constructor
  · intro h mode ha
    exact h ⟨mode, ha⟩
  · intro h ⟨mode, ha⟩
    exact h mode ha

instance {d : Nat} (A : Word d 3 → Bool) : Decidable (IsGeomLineFree A) :=
  decidable_of_iff
    (∀ mode : Fin d → GeomMode, (∃ i : Fin d, mode i = .pos ∨ mode i = .neg) →
      ∃ t : Fin 3, A (evalGeomMask mode t) = false)
    (isGeomLineFree_iff_mode A).symm

/-- Every geometric-line-free subset is also combinatorial-line-free (`c'_{d, 3} ≤ c_{d, 3}`). -/
theorem isGeomLineFree_implies_isLineFree {d : Nat} {A : Word d 3 → Bool}
    (h : IsGeomLineFree A) : IsLineFree A := by
  intro L
  let g : GeomLine d := {
    mode := fun i => match L.mask i with | some a => .const a | none => .pos
    hasActive := by
      obtain ⟨i, hi⟩ := L.hasWildcard
      exact ⟨i, Or.inl (by simp [hi])⟩
  }
  obtain ⟨t, ht⟩ := h g
  refine ⟨t, ?_⟩
  have hev : g.eval t = L.eval t := by
    funext i
    cases hm : L.mask i <;> simp [g, GeomLine.eval, evalGeomMask, Line.eval, evalMask, evalGeomMode, hm]
  rwa [← hev]

private def consGeomLine {d : Nat} (a : Fin 3) (L : GeomLine d) : GeomLine (d + 1) where
  mode := consFin (.const a) L.mode
  hasActive := by
    obtain ⟨i, hi⟩ := L.hasActive
    exact ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, by simpa [consFin] using hi⟩

private theorem consGeomLine_eval {d : Nat} (a : Fin 3) (L : GeomLine d) (t : Fin 3) :
    (consGeomLine a L).eval t = consFin a (L.eval t) := by
  funext ⟨v, hv⟩
  cases v <;> rfl

/-- Slice submultiplicativity for geometric-line-free subsets: `c'_{d+1, 3} ≤ 3 * c'_{d, 3}`. -/
theorem geomLineFree_slice_bound {d M : Nat}
    (h : ∀ B : Word d 3 → Bool, IsGeomLineFree B → wordCard B ≤ M)
    (A : Word (d + 1) 3 → Bool) (hA : IsGeomLineFree A) :
    wordCard A ≤ 3 * M := by
  simp only [wordCard]
  refine sumFin_le_mul 3 M _ ?_
  intro a
  refine h (fun w => A (consFin a w)) ?_
  intro L
  obtain ⟨t, ht⟩ := hA (consGeomLine a L)
  rw [consGeomLine_eval] at ht
  exact ⟨t, ht⟩

theorem moser_1_3_upper : ∀ A : Word 1 3 → Bool, IsGeomLineFree A → wordCard A ≤ 2 :=
  fun _ h => by
    have : ∀ A : Word 1 3 → Bool, IsLineFree A → wordCard A ≤ 2 := by decide
    exact this _ (isGeomLineFree_implies_isLineFree h)

private def moser_1_3_set (w : Word 1 3) : Bool :=
  (w ⟨0, by decide⟩).val < 2

theorem moser_1_3_lower : ∃ A : Word 1 3 → Bool, IsGeomLineFree A ∧ wordCard A = 2 := by
  refine ⟨moser_1_3_set, ?_, ?_⟩
  · decide
  · decide

theorem moser_1_3_exact :
    (∀ A : Word 1 3 → Bool, IsGeomLineFree A → wordCard A ≤ 2) ∧
    (∃ A : Word 1 3 → Bool, IsGeomLineFree A ∧ wordCard A = 2) :=
  ⟨moser_1_3_upper, moser_1_3_lower⟩

theorem moser_2_3_upper : ∀ A : Word 2 3 → Bool, IsGeomLineFree A → wordCard A ≤ 6 :=
  geomLineFree_slice_bound moser_1_3_upper

theorem moser_2_3_lower : ∃ A : Word 2 3 → Bool, IsGeomLineFree A ∧ wordCard A = 6 := by
  refine ⟨decode2 ⟨238, by decide⟩, ?_, ?_⟩
  · decide
  · decide

theorem moser_2_3_exact :
    (∀ A : Word 2 3 → Bool, IsGeomLineFree A → wordCard A ≤ 6) ∧
    (∃ A : Word 2 3 → Bool, IsGeomLineFree A ∧ wordCard A = 6) :=
  ⟨moser_2_3_upper, moser_2_3_lower⟩

private def isGLF2 (m : Fin 512) : Bool :=
  decide (IsGeomLineFree (decode2 m))

private theorem glf2_size6_edges :
    ∀ m : Fin 512, 6 ≤ card2 m → isGLF2 m = true →
      decode2 m (w2OfIdx ⟨1, by decide⟩) = true ∧
      decode2 m (w2OfIdx ⟨3, by decide⟩) = true ∧
      decode2 m (w2OfIdx ⟨5, by decide⟩) = true ∧
      decode2 m (w2OfIdx ⟨7, by decide⟩) = true :=
  forall_fin512 fun a b c => by
    revert a b c
    decide

private theorem glf2_size5_has_edge :
    ∀ m : Fin 512, 5 ≤ card2 m → isGLF2 m = true →
      decode2 m (w2OfIdx ⟨1, by decide⟩) = true ∨
      decode2 m (w2OfIdx ⟨3, by decide⟩) = true ∨
      decode2 m (w2OfIdx ⟨5, by decide⟩) = true ∨
      decode2 m (w2OfIdx ⟨7, by decide⟩) = true :=
  forall_fin512 fun a b c => by
    revert a b c
    decide

private theorem slice_isGeomLineFree {d : Nat} {A : Word (d + 1) 3 → Bool} (hA : IsGeomLineFree A)
    (a : Fin 3) : IsGeomLineFree (fun w => A (consFin a w)) := by
  intro L
  obtain ⟨t, ht⟩ := hA (consGeomLine a L)
  rw [consGeomLine_eval] at ht
  exact ⟨t, ht⟩

private def vertGeomLine3 (w : Word 2 3) : GeomLine 3 where
  mode := consFin .pos (fun i => .const (w i))
  hasActive := ⟨⟨0, by decide⟩, Or.inl rfl⟩

private theorem vertGeomLine3_eval (w : Word 2 3) (t : Fin 3) :
    (vertGeomLine3 w).eval t = consFin t w := by
  funext ⟨v, hv⟩
  cases v <;> rfl

private theorem vert_edge_impossible (B : Word 3 3 → Bool) (hB : IsGeomLineFree B)
    (w : Word 2 3)
    (h0 : B (consFin ⟨0, by decide⟩ w) = true)
    (h1 : B (consFin ⟨1, by decide⟩ w) = true)
    (h2 : B (consFin ⟨2, by decide⟩ w) = true) : False := by
  obtain ⟨t, ht⟩ := hB (vertGeomLine3 w)
  rw [vertGeomLine3_eval] at ht
  have htv := t.isLt
  match hv : t.val with
  | 0 =>
    have ht0 : t = ⟨0, by decide⟩ := Fin.ext hv
    rw [ht0] at ht
    simp_all
  | 1 =>
    have ht1 : t = ⟨1, by decide⟩ := Fin.ext hv
    rw [ht1] at ht
    simp_all
  | 2 =>
    have ht2 : t = ⟨2, by decide⟩ := Fin.ext hv
    rw [ht2] at ht
    simp_all
  | _ + 3 => omega

/-- **Moser Number `c'_{3, 3} ≤ 16`**: no geometric-line-free subset of `[3]^3` has size `≥ 17`. -/
theorem moser_3_3_upper : ∀ B : Word 3 3 → Bool, IsGeomLineFree B → wordCard B ≤ 16 := by
  intro B hB
  let B0 : Word 2 3 → Bool := fun w => B (consFin ⟨0, by decide⟩ w)
  let B1 : Word 2 3 → Bool := fun w => B (consFin ⟨1, by decide⟩ w)
  let B2 : Word 2 3 → Bool := fun w => B (consFin ⟨2, by decide⟩ w)
  have hf0 : IsGeomLineFree B0 := slice_isGeomLineFree hB ⟨0, by decide⟩
  have hf1 : IsGeomLineFree B1 := slice_isGeomLineFree hB ⟨1, by decide⟩
  have hf2 : IsGeomLineFree B2 := slice_isGeomLineFree hB ⟨2, by decide⟩
  have hb0 : wordCard B0 ≤ 6 := moser_2_3_upper B0 hf0
  have hb1 : wordCard B1 ≤ 6 := moser_2_3_upper B1 hf1
  have hb2 : wordCard B2 ≤ 6 := moser_2_3_upper B2 hf2
  have hsum : wordCard B = wordCard B0 + wordCard B1 + wordCard B2 := wordCard_succ3 B
  by_cases h17 : 17 ≤ wordCard B
  · exfalso
    have hcase : (6 ≤ wordCard B0 ∧ 6 ≤ wordCard B1 ∧ 5 ≤ wordCard B2) ∨
        (6 ≤ wordCard B0 ∧ 6 ≤ wordCard B2 ∧ 5 ≤ wordCard B1) ∨
        (6 ≤ wordCard B1 ∧ 6 ≤ wordCard B2 ∧ 5 ≤ wordCard B0) := by omega
    have hgl0 : isGLF2 (encode2 B0) = true := by
      dsimp [isGLF2]; rw [decode2_encode2]; exact decide_eq_true hf0
    have hgl1 : isGLF2 (encode2 B1) = true := by
      dsimp [isGLF2]; rw [decode2_encode2]; exact decide_eq_true hf1
    have hgl2 : isGLF2 (encode2 B2) = true := by
      dsimp [isGLF2]; rw [decode2_encode2]; exact decide_eq_true hf2
    rcases hcase with ⟨h0, h1, h2⟩ | ⟨h0, h2, h1⟩ | ⟨h1, h2, h0⟩
    · have e0 := glf2_size6_edges (encode2 B0) (by rw [← wordCard_eq_card2_encode2]; exact h0) hgl0
      have e1 := glf2_size6_edges (encode2 B1) (by rw [← wordCard_eq_card2_encode2]; exact h1) hgl1
      have e2 := glf2_size5_has_edge (encode2 B2) (by rw [← wordCard_eq_card2_encode2]; exact h2) hgl2
      rw [decode2_encode2] at e0 e1 e2
      rcases e2 with h | h | h | h
      · exact vert_edge_impossible B hB _ e0.1 e1.1 h
      · exact vert_edge_impossible B hB _ e0.2.1 e1.2.1 h
      · exact vert_edge_impossible B hB _ e0.2.2.1 e1.2.2.1 h
      · exact vert_edge_impossible B hB _ e0.2.2.2 e1.2.2.2 h
    · have e0 := glf2_size6_edges (encode2 B0) (by rw [← wordCard_eq_card2_encode2]; exact h0) hgl0
      have e2 := glf2_size6_edges (encode2 B2) (by rw [← wordCard_eq_card2_encode2]; exact h2) hgl2
      have e1 := glf2_size5_has_edge (encode2 B1) (by rw [← wordCard_eq_card2_encode2]; exact h1) hgl1
      rw [decode2_encode2] at e0 e1 e2
      rcases e1 with h | h | h | h
      · exact vert_edge_impossible B hB _ e0.1 h e2.1
      · exact vert_edge_impossible B hB _ e0.2.1 h e2.2.1
      · exact vert_edge_impossible B hB _ e0.2.2.1 h e2.2.2.1
      · exact vert_edge_impossible B hB _ e0.2.2.2 h e2.2.2.2
    · have e1 := glf2_size6_edges (encode2 B1) (by rw [← wordCard_eq_card2_encode2]; exact h1) hgl1
      have e2 := glf2_size6_edges (encode2 B2) (by rw [← wordCard_eq_card2_encode2]; exact h2) hgl2
      have e0 := glf2_size5_has_edge (encode2 B0) (by rw [← wordCard_eq_card2_encode2]; exact h0) hgl0
      rw [decode2_encode2] at e0 e1 e2
      rcases e0 with h | h | h | h
      · exact vert_edge_impossible B hB _ h e1.1 e2.1
      · exact vert_edge_impossible B hB _ h e1.2.1 e2.2.1
      · exact vert_edge_impossible B hB _ h e1.2.2.1 e2.2.2.1
      · exact vert_edge_impossible B hB _ h e1.2.2.2 e2.2.2.2
  · omega

private def countGeomConst : ∀ {d : Nat}, Fin 3 → (Fin d → GeomMode) → Nat
  | 0, _, _ => 0
  | _ + 1, a, mode =>
    (if mode ⟨0, Nat.zero_lt_succ _⟩ = .const a then 1 else 0) +
      countGeomConst a (fun i => mode ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private def countGeomPos : ∀ {d : Nat}, (Fin d → GeomMode) → Nat
  | 0, _ => 0
  | _ + 1, mode =>
    (if mode ⟨0, Nat.zero_lt_succ _⟩ = .pos then 1 else 0) +
      countGeomPos (fun i => mode ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private def countGeomNeg : ∀ {d : Nat}, (Fin d → GeomMode) → Nat
  | 0, _ => 0
  | _ + 1, mode =>
    (if mode ⟨0, Nat.zero_lt_succ _⟩ = .neg then 1 else 0) +
      countGeomNeg (fun i => mode ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private theorem countGeom_sum :
    ∀ {d : Nat} (mode : Fin d → GeomMode),
      countGeomConst ⟨0, by decide⟩ mode +
      countGeomConst ⟨1, by decide⟩ mode +
      countGeomConst ⟨2, by decide⟩ mode +
      countGeomPos mode +
      countGeomNeg mode = d
  | 0, _ => rfl
  | d + 1, mode => by
    have ih := countGeom_sum (fun i : Fin d => mode ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    dsimp only [countGeomConst, countGeomPos, countGeomNeg]
    cases hm : mode ⟨0, Nat.zero_lt_succ d⟩ with
    | pos =>
      simp at ih ⊢
      omega
    | neg =>
      simp at ih ⊢
      omega
    | const x =>
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

private theorem countGeomActive_pos :
    ∀ {d : Nat} (mode : Fin d → GeomMode),
      (∃ i : Fin d, mode i = .pos ∨ mode i = .neg) →
        1 ≤ countGeomPos mode + countGeomNeg mode
  | 0, _, ⟨i, _⟩ => i.elim0
  | d + 1, mode, ⟨⟨v, hv⟩, ha⟩ => by
    dsimp only [countGeomPos, countGeomNeg]
    cases v with
    | zero =>
      rcases ha with hpos | hneg
      · simp only [hpos, ↓reduceIte]; omega
      · simp only [hneg, ↓reduceIte]; omega
    | succ v' =>
      have ih := countGeomActive_pos (fun i : Fin d => mode ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        ⟨⟨v', Nat.lt_of_succ_lt_succ hv⟩, ha⟩
      omega

private theorem letterCount_evalGeomMask_eq :
    ∀ {d : Nat} (a t : Fin 3) (mode : Fin d → GeomMode),
      letterCount a (evalGeomMask mode t) =
        countGeomConst a mode +
          (if t = a then countGeomPos mode else 0) +
          (if negFin3 t = a then countGeomNeg mode else 0)
  | 0, _, _, _ => by
    simp [letterCount, countGeomConst, countGeomPos, countGeomNeg]
  | d + 1, a, t, mode => by
    have ih := letterCount_evalGeomMask_eq a t (fun i : Fin d => mode ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    dsimp only [letterCount, countGeomConst, countGeomPos, countGeomNeg, evalGeomMask]
    change (if evalGeomMode (mode ⟨0, Nat.zero_lt_succ d⟩) t = a then 1 else 0) +
      letterCount a (evalGeomMask (fun i : Fin d => mode ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) t) = _
    rw [ih]
    cases mode ⟨0, Nat.zero_lt_succ d⟩ with
    | pos =>
      dsimp only [evalGeomMode]
      by_cases ht : t = a <;> simp [ht] <;> omega
    | neg =>
      dsimp only [evalGeomMode]
      by_cases hnt : negFin3 t = a <;> simp [hnt] <;> omega
    | const x =>
      dsimp only [evalGeomMode]
      by_cases hx : x = a <;> simp [hx] <;> omega

/-- Check geometric-line-freeness of `fujimuraSet d T` directly over count/direction tuples `(a, b, c, p)`. -/
def checkGeomSimplexFree (d : Nat) (T : Nat → Nat → Nat → Bool) : Bool :=
  decide (∀ a b c p : Fin (d + 1),
    a.val + b.val + c.val < d ∧ a.val + b.val + c.val + p.val ≤ d →
      let q := d - (a.val + b.val + c.val + p.val)
      !(T (a.val + p.val) b.val (c.val + q) &&
        T a.val (b.val + p.val + q) c.val &&
        T (a.val + q) b.val (c.val + p.val)))

theorem geom_fujimura_isGeomLineFree (d : Nat) (T : Nat → Nat → Nat → Bool)
    (hT : checkGeomSimplexFree d T = true) : IsGeomLineFree (fujimuraSet d T) := by
  intro L
  have hall := of_decide_eq_true hT
  let a := countGeomConst ⟨0, by decide⟩ L.mode
  let b := countGeomConst ⟨1, by decide⟩ L.mode
  let c := countGeomConst ⟨2, by decide⟩ L.mode
  let p := countGeomPos L.mode
  let q := countGeomNeg L.mode
  have hsum : a + b + c + p + q = d := countGeom_sum L.mode
  have hpq : 1 ≤ p + q := countGeomActive_pos L.mode L.hasActive
  have hlt : a + b + c < d := by omega
  have hle : a + b + c + p ≤ d := by omega
  have hnot := hall ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨p, by omega⟩ ⟨hlt, hle⟩
  have hqeq : d - (a + b + c + p) = q := by omega
  dsimp only at hnot
  rw [hqeq] at hnot
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
        dsimp only [fujimuraSet, GeomLine.eval] at ht0 ht1 ht2
        rw [letterCount_evalGeomMask_eq ⟨0, by decide⟩ ⟨0, by decide⟩ L.mode,
            letterCount_evalGeomMask_eq ⟨1, by decide⟩ ⟨0, by decide⟩ L.mode,
            letterCount_evalGeomMask_eq ⟨2, by decide⟩ ⟨0, by decide⟩ L.mode] at ht0
        rw [letterCount_evalGeomMask_eq ⟨0, by decide⟩ ⟨1, by decide⟩ L.mode,
            letterCount_evalGeomMask_eq ⟨1, by decide⟩ ⟨1, by decide⟩ L.mode,
            letterCount_evalGeomMask_eq ⟨2, by decide⟩ ⟨1, by decide⟩ L.mode] at ht1
        rw [letterCount_evalGeomMask_eq ⟨0, by decide⟩ ⟨2, by decide⟩ L.mode,
            letterCount_evalGeomMask_eq ⟨1, by decide⟩ ⟨2, by decide⟩ L.mode,
            letterCount_evalGeomMask_eq ⟨2, by decide⟩ ⟨2, by decide⟩ L.mode] at ht2
        have hneg0 : negFin3 0 = 2 := by decide
        have hneg1 : negFin3 1 = 1 := by decide
        have hneg2 : negFin3 2 = 0 := by decide
        have hp0 : T (a + p) b (c + q) = true := by
          simpa [a, b, c, p, q, hneg0] using ht0
        have hp1 : T a (b + p + q) c = true := by
          have hsub : b + p + q = b + (p + q) := by omega
          simpa [a, b, c, p, q, hneg1, hsub] using ht1
        have hp2 : T (a + q) b (c + p) = true := by
          simpa [a, b, c, p, q, hneg2] using ht2
        rw [hp0, hp1, hp2] at hnot
        simp at hnot

theorem moser_fujimura_lower_bound (d size : Nat) (triples : List (Nat × Nat × Nat))
    (hFree : checkGeomSimplexFree d (triplePred triples) = true)
    (hCard : fujimuraCard d (triplePred triples) = size) :
    ∃ A : Word d 3 → Bool, IsGeomLineFree A ∧ wordCard A = size := by
  refine ⟨fujimuraSet d (triplePred triples), geom_fujimura_isGeomLineFree d _ hFree, ?_⟩
  rw [wordCard_fujimuraSet, hCard]

private def moser_d3_triples : List (Nat × Nat × Nat) :=
  [(0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 1, 0), (3, 0, 0)]

theorem moser_3_3_lower : ∃ B : Word 3 3 → Bool, IsGeomLineFree B ∧ wordCard B = 16 :=
  moser_fujimura_lower_bound 3 16 moser_d3_triples (by decide) (by decide)

theorem moser_3_3_exact :
    (∀ B : Word 3 3 → Bool, IsGeomLineFree B → wordCard B ≤ 16) ∧
    (∃ B : Word 3 3 → Bool, IsGeomLineFree B ∧ wordCard B = 16) :=
  ⟨moser_3_3_upper, moser_3_3_lower⟩

/-- Strict separation in `[3]^3`: Moser max `c'_{3, 3} = 16` vs Polymath-1 combinatorial max `c_{3, 3} = 18`. -/
theorem moser_3_3_strict_gap :
    (∀ B : Word 3 3 → Bool, IsGeomLineFree B → wordCard B ≤ 16) ∧
    (∃ B : Word 3 3 → Bool, IsLineFree B ∧ wordCard B = 18) :=
  ⟨moser_3_3_upper, c_3_3_lower⟩

theorem moser_4_3_upper_48 : ∀ A : Word 4 3 → Bool, IsGeomLineFree A → wordCard A ≤ 48 :=
  geomLineFree_slice_bound moser_3_3_upper

private def moser_d4_triples : List (Nat × Nat × Nat) :=
  [(0, 1, 3), (1, 0, 3), (1, 1, 2), (1, 2, 1), (2, 2, 0), (3, 1, 0), (4, 0, 0)]

/-- Explicit 43-point geometric-line-free witness in `[3]^4` (`c'_{4, 3} ≥ 43`). -/
theorem moser_4_3_ge_43 : ∃ A : Word 4 3 → Bool, IsGeomLineFree A ∧ wordCard A = 43 :=
  moser_fujimura_lower_bound 4 43 moser_d4_triples (by decide) (by decide)

end HJBrigade
