import HJBrigade.GraphRamsey.Basic
import HJBrigade.Certificates.HypergraphCert

/-!
# Schur's Theorem, Ramsey-to-Schur Reduction & Hypergraph Schur Certificates

Formalizes Schur's theorem on monochromatic solutions to `x + y = z` in `{1, …, n}`:
- `HasMonoSchurFor`, `HasMonoSchur`, and `hasMonoSchur_iff_for`
- Constructive proof `multicolor_ramsey_implies_schur` from `MulticolorRamseyUpper N r 3`
- Unconditional `schur_theorem` for every `r ≥ 1`
- Parameterized `HyperCert` reflection checker `checkSchurCertSym_sound`
- Exact small Schur bounds `S(1) = 2` and `S(2) = 5`
-/

namespace HJBrigade

/-- A coloring `c : Fin n → Fin r` (representing `1..n` via `.val + 1`) contains a
monochromatic Schur triple `x + y = z` (`x ≤ y` allowed). -/
def HasMonoSchurFor (n r : Nat) (c : Fin n → Fin r) : Prop :=
  ∃ x y z : Fin n, (x.val + 1) + (y.val + 1) = z.val + 1 ∧ c x = c y ∧ c x = c z

/-- Every `r`-coloring of `{1, …, n}` contains a monochromatic Schur triple. -/
def HasMonoSchur (n r : Nat) : Prop :=
  ∀ c : Fin n → Fin r, HasMonoSchurFor n r c

theorem hasMonoSchur_iff_for (n r : Nat) :
    HasMonoSchur n r ↔ ∀ c : Fin n → Fin r, HasMonoSchurFor n r c := Iff.rfl

instance (n r : Nat) (c : Fin n → Fin r) : Decidable (HasMonoSchurFor n r c) :=
  inferInstanceAs (Decidable (∃ x y z : Fin n,
    (x.val + 1) + (y.val + 1) = z.val + 1 ∧ c x = c y ∧ c x = c z))

/-- **Ramsey → Schur Reduction**: `MulticolorRamseyUpper (n + 1) r 3` implies `HasMonoSchur n r`. -/
theorem multicolor_ramsey_implies_schur {N r : Nat} (hr : r ≥ 1) (hN : N ≥ 2)
    (hR : MulticolorRamseyUpper N r 3) :
    HasMonoSchur (N - 1) r := by
  intro c
  let edgeC (u v : Fin N) : Fin r :=
    if hu : u.val < v.val then c ⟨v.val - u.val - 1, by omega⟩
    else if hv : v.val < u.val then c ⟨u.val - v.val - 1, by omega⟩
    else ⟨0, hr⟩
  obtain ⟨col, f, hfMono, hfC⟩ := hR edgeC
  have h01 : (f 0).val < (f 1).val := hfMono 0 1 (by decide)
  have h12 : (f 1).val < (f 2).val := hfMono 1 2 (by decide)
  have h02 : (f 0).val < (f 2).val := Nat.lt_trans h01 h12
  let x : Fin (N - 1) := ⟨(f 1).val - (f 0).val - 1, by have := (f 1).isLt; omega⟩
  let y : Fin (N - 1) := ⟨(f 2).val - (f 1).val - 1, by have := (f 2).isLt; omega⟩
  let z : Fin (N - 1) := ⟨(f 2).val - (f 0).val - 1, by have := (f 2).isLt; omega⟩
  have h01c : edgeC (f 0) (f 1) = col := hfC 0 1 (by decide)
  have h12c : edgeC (f 1) (f 2) = col := hfC 1 2 (by decide)
  have h02c : edgeC (f 0) (f 2) = col := hfC 0 2 (by decide)
  have cx : c x = col := by
    have he : edgeC (f 0) (f 1) = c x := by simp [edgeC, h01, x]
    exact he.symm.trans h01c
  have cy : c y = col := by
    have he : edgeC (f 1) (f 2) = c y := by simp [edgeC, h12, y]
    exact he.symm.trans h12c
  have cz : c z = col := by
    have he : edgeC (f 0) (f 2) = c z := by simp [edgeC, h02, z]
    exact he.symm.trans h02c
  refine ⟨x, y, z, ?_, cx.trans cy.symm, cx.trans cz.symm⟩
  dsimp only [x, y, z]
  omega

/-- **Schur's Theorem**: for every `r ≥ 1`, there exists `n ≥ 1` with `HasMonoSchur n r`. -/
theorem schur_theorem (r : Nat) (hr : r ≥ 1) :
    ∃ n : Nat, n ≥ 1 ∧ HasMonoSchur n r := by
  obtain ⟨N, _hN, hR⟩ := ramsey_multicolor_triangles r hr
  if hN3 : N ≥ 3 then
    exact ⟨N - 1, by omega, multicolor_ramsey_implies_schur hr (by omega) hR⟩
  else
    exfalso
    obtain ⟨_, f, hfMono, _⟩ := hR (fun _ _ => ⟨0, hr⟩)
    have h01 := hfMono 0 1 (by decide)
    have h12 := hfMono 1 2 (by decide)
    have h2lt := (f 2).isLt
    omega

-- ============================================================================
-- HyperCert Soundness Bridge for Exact Schur Upper Bounds
-- ============================================================================

def schurValidTriple (n : Nat) (w : Nat × Nat × Nat) : Bool :=
  decide (w.1 < n ∧ w.2.1 < n ∧ w.2.2 < n ∧ (w.1 + 1) + (w.2.1 + 1) = w.2.2 + 1)

def schurTriplePts (w : Nat × Nat × Nat) : List Nat :=
  [w.1, w.2.1, w.2.2]

theorem checkSchurCertSym_sound (n r : Nat) (hr : r ≥ 1) (rootV : Nat) (hroot : rootV < n)
    (tree : HyperCert (Nat × Nat × Nat) r)
    (h : checkHyperCert n r (schurValidTriple n) schurTriplePts tree [(rootV, 0)] = true) :
    HasMonoSchur n r := by
  intro c
  obtain ⟨w, hwValid, col, hmono⟩ :=
    checkHyperCertSym_sound n r hr rootV hroot (schurValidTriple n) schurTriplePts tree h c
  simp only [schurValidTriple, decide_eq_true_eq] at hwValid
  obtain ⟨hxLt, hyLt, hzLt, hsum⟩ := hwValid
  obtain ⟨hxV, hcx⟩ := hmono w.1 (by simp [schurTriplePts])
  obtain ⟨hyV, hcy⟩ := hmono w.2.1 (by simp [schurTriplePts])
  obtain ⟨hzV, hcz⟩ := hmono w.2.2 (by simp [schurTriplePts])
  exact ⟨⟨w.1, hxLt⟩, ⟨w.2.1, hyLt⟩, ⟨w.2.2, hzLt⟩, hsum,
    hcx.trans hcy.symm, hcx.trans hcz.symm⟩

-- ============================================================================
-- Exact Small Schur Numbers: S(1) = 2, S(2) = 5
-- ============================================================================

private def schur_1_1_witness (_ : Fin 1) : Fin 1 := ⟨0, by decide⟩

theorem schur_1_gt_1 : ¬ HasMonoSchur 1 1 := by
  intro h
  have h1 : HasMonoSchurFor 1 1 schur_1_1_witness :=
    (hasMonoSchur_iff_for 1 1).mp h schur_1_1_witness
  revert h1
  decide

theorem schur_1_le_2 : HasMonoSchur 2 1 := by
  intro c
  exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, rfl, rfl,
    Fin.ext (by have h0 := (c 0).isLt; have h1 := (c 1).isLt; omega)⟩

theorem schur_1_exact : ¬ HasMonoSchur 1 1 ∧ HasMonoSchur 2 1 :=
  ⟨schur_1_gt_1, schur_1_le_2⟩

private def schur_4_2_witness (i : Fin 4) : Fin 2 :=
  ⟨([0, 1, 1, 0].getD i.val 0) % 2, Nat.mod_lt _ (by decide)⟩

theorem schur_2_gt_4 : ¬ HasMonoSchur 4 2 := by
  intro h
  have h4 : HasMonoSchurFor 4 2 schur_4_2_witness :=
    (hasMonoSchur_iff_for 4 2).mp h schur_4_2_witness
  revert h4
  decide

private def schur_5_2_cert : HyperCert (Nat × Nat × Nat) 2 :=
  HyperCert.split 1 [
    HyperCert.witness (0, 0, 1) 0,
    HyperCert.split 2 [
      HyperCert.split 3 [
        HyperCert.witness (0, 2, 3) 0,
        HyperCert.witness (1, 1, 3) 1
      ],
      HyperCert.split 3 [
        HyperCert.split 4 [
          HyperCert.witness (0, 3, 4) 0,
          HyperCert.witness (1, 2, 4) 1
        ],
        HyperCert.witness (1, 1, 3) 1
      ]
    ]
  ]

theorem schur_2_le_5 : HasMonoSchur 5 2 := by
  have h : checkHyperCert 5 2 (schurValidTriple 5) schurTriplePts schur_5_2_cert [(0, 0)] = true := by
    decide
  exact checkSchurCertSym_sound 5 2 (by decide) 0 (by decide) schur_5_2_cert h

theorem schur_2_exact : ¬ HasMonoSchur 4 2 ∧ HasMonoSchur 5 2 :=
  ⟨schur_2_gt_4, schur_2_le_5⟩

end HJBrigade
