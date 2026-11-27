import HJBrigade.GraphRamsey.Basic

/-!
# Exact Finite Graph & Multicolor Ramsey Numbers

Formalizes exact upper bounds (constructive + Greenwood–Gleason parity tightening)
and exact finite counterexample witnesses checked via `checkNoClique_sound` /
`checkNoMonoClique_sound` using kernel `decide` (zero `native_decide`, zero `sorry`,
zero extra axioms):
- `R(3, 3) = 6` (`ramsey_3_3_exact`)
- `R(3, 4) = 9` (`ramsey_3_4_exact`)
- `R(3, 5) = 14` (`ramsey_3_5_exact`)
- `R(4, 4) = 18` (`ramsey_4_4_exact`)
- `R(3, 3, 3) = 17` (`ramsey_3_3_3_exact`)
-/

namespace HJBrigade

/-- Any 2-color diagonal Ramsey bound `GraphRamseyUpper N k k` yields `MulticolorRamseyUpper N 2 k`. -/
theorem graphRamsey_to_multicolor2 {N k : Nat} (h : GraphRamseyUpper N k k) :
    MulticolorRamseyUpper N 2 k := by
  intro c
  let G : Fin N → Fin N → Bool := fun u v => decide (c u v = ⟨1, by decide⟩)
  rcases h G with ⟨f, hfMono, hfC⟩ | ⟨g, hgMono, hgC⟩
  · refine ⟨⟨0, by decide⟩, f, hfMono, fun i j hij => ?_⟩
    have hfalse : G (f i) (f j) = false := hfC i j hij
    have hne : c (f i) (f j) ≠ ⟨1, by decide⟩ := by
      intro heq
      have htrue : G (f i) (f j) = true := decide_eq_true heq
      rw [hfalse] at htrue
      cases htrue
    apply Fin.ext
    have hlt := (c (f i) (f j)).isLt
    have hneVal : (c (f i) (f j)).val ≠ 1 := fun hv => hne (Fin.ext hv)
    dsimp only
    omega
  · refine ⟨⟨1, by decide⟩, g, hgMono, fun i j hij => ?_⟩
    have htrue : G (g i) (g j) = true := hgC i j hij
    exact of_decide_eq_true htrue

-- ============================================================================
-- R(3, 3) = 6
-- ============================================================================

theorem ramsey_3_3_upper : GraphRamseyUpper 6 3 3 :=
  erdos_szekeres_step (ramsey_left_two 3 (by decide)) (ramsey_right_two 3 (by decide))
    (by decide) (by decide)

def ramsey33Witness (u v : Fin 5) : Bool :=
  let d := (v.val + 5 - u.val) % 5
  !(d == 1 || d == 4)

theorem ramsey_3_3_lower : ¬ GraphRamseyUpper 5 3 3 :=
  checkNoClique_sound ramsey33Witness (by decide) (by decide)

theorem ramsey_3_3_exact : GraphRamseyUpper 6 3 3 ∧ ¬ GraphRamseyUpper 5 3 3 :=
  ⟨ramsey_3_3_upper, ramsey_3_3_lower⟩

theorem ramsey_3_3_multicolor_upper : MulticolorRamseyUpper 6 2 3 :=
  graphRamsey_to_multicolor2 ramsey_3_3_upper

-- ============================================================================
-- R(3, 4) = 9 (Greenwood–Gleason Parity Tightening + Z/8Z Witness)
-- ============================================================================

theorem ramsey_3_4_upper : GraphRamseyUpper 9 3 4 :=
  erdos_szekeres_even (ramsey_left_two 4 (by decide)) ramsey_3_3_upper
    (by decide) (by decide) (by decide) (by decide)

def ramsey34Witness (u v : Fin 8) : Bool :=
  let d := (v.val + 8 - u.val) % 8
  !(d == 1 || d == 4 || d == 7)

theorem ramsey_3_4_lower : ¬ GraphRamseyUpper 8 3 4 :=
  checkNoClique_sound ramsey34Witness (by decide) (by decide)

theorem ramsey_3_4_exact : GraphRamseyUpper 9 3 4 ∧ ¬ GraphRamseyUpper 8 3 4 :=
  ⟨ramsey_3_4_upper, ramsey_3_4_lower⟩

-- ============================================================================
-- R(3, 5) = 14 (Erdős–Szekeres Step + Z/13Z Cubic-like Circulant Witness)
-- ============================================================================

theorem ramsey_3_5_upper : GraphRamseyUpper 14 3 5 :=
  erdos_szekeres_step (ramsey_left_two 5 (by decide)) ramsey_3_4_upper
    (by decide) (by decide)

def ramsey35Witness (u v : Fin 13) : Bool :=
  let d := (v.val + 13 - u.val) % 13
  !(d == 1 || d == 5 || d == 8 || d == 12)

theorem ramsey_3_5_lower : ¬ GraphRamseyUpper 13 3 5 :=
  checkNoClique_sound ramsey35Witness (by decide) (by decide)

theorem ramsey_3_5_exact : GraphRamseyUpper 14 3 5 ∧ ¬ GraphRamseyUpper 13 3 5 :=
  ⟨ramsey_3_5_upper, ramsey_3_5_lower⟩

-- ============================================================================
-- R(4, 4) = 18 (Symmetry Step from R(3, 4) = 9 + Paley Graph P_17)
-- ============================================================================

theorem ramsey_4_4_upper : GraphRamseyUpper 18 4 4 :=
  erdos_szekeres_step (M1 := 9) (M2 := 9) ramsey_3_4_upper ramsey_3_4_upper.symm (by decide) (by decide)

def ramsey44Witness (u v : Fin 17) : Bool :=
  let d := (v.val + 17 - u.val) % 17
  !(d == 1 || d == 2 || d == 4 || d == 8 || d == 9 || d == 13 || d == 15 || d == 16)

theorem ramsey_4_4_lower : ¬ GraphRamseyUpper 17 4 4 :=
  checkNoClique_sound ramsey44Witness (by decide) (by decide)

theorem ramsey_4_4_exact : GraphRamseyUpper 18 4 4 ∧ ¬ GraphRamseyUpper 17 4 4 :=
  ⟨ramsey_4_4_upper, ramsey_4_4_lower⟩

-- ============================================================================
-- R(3, 3, 3) = 17 (Greenwood–Gleason 3-Color Triangle + GF(16) Coset Witness)
-- ============================================================================

theorem ramsey_3_3_3_upper : MulticolorRamseyUpper 17 3 3 :=
  ramsey_triangle_step (M := 6) (r := 2) (by decide) (by decide) ramsey_3_3_multicolor_upper

private def xor4 (a b : Nat) : Nat :=
  (a + b) % 2 +
  2 * (((a / 2) + (b / 2)) % 2) +
  4 * (((a / 4) + (b / 4)) % 2) +
  8 * (((a / 8) + (b / 8)) % 2)

private def gf16LogMod3 : Nat → Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨0, by decide⟩
  | 2 => ⟨1, by decide⟩
  | 3 => ⟨1, by decide⟩
  | 4 => ⟨2, by decide⟩
  | 5 => ⟨2, by decide⟩
  | 6 => ⟨2, by decide⟩
  | 7 => ⟨1, by decide⟩
  | 8 => ⟨0, by decide⟩
  | 9 => ⟨2, by decide⟩
  | 10 => ⟨0, by decide⟩
  | 11 => ⟨1, by decide⟩
  | 12 => ⟨0, by decide⟩
  | 13 => ⟨1, by decide⟩
  | 14 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def ramsey333Witness (u v : Fin 16) : Fin 3 :=
  gf16LogMod3 (xor4 u.val v.val)

theorem ramsey_3_3_3_lower : ¬ MulticolorRamseyUpper 16 3 3 :=
  checkNoMonoClique_sound ramsey333Witness (by decide)

theorem ramsey_3_3_3_exact : MulticolorRamseyUpper 17 3 3 ∧ ¬ MulticolorRamseyUpper 16 3 3 :=
  ⟨ramsey_3_3_3_upper, ramsey_3_3_3_lower⟩

end HJBrigade
