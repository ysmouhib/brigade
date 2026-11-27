import HJBrigade.Certificates.CertTree
import HJBrigade.Reductions.VanDerWaerden

/-!
# Parameterized Hypergraph DPLL Reflection Certificates (`HyperCert W r`)

Generalizes `CertTree` from Hales–Jewett combinatorial lines to arbitrary finite
`r`-colored hypergraphs `(V, edges : W → List Nat)`. Used to kernel-verify upper bounds for:
- Van der Waerden progressions (`checkVdWCertSym_sound`, e.g. `W(4, 2) = 35`)
- Schur triples (`checkSchurCertSym_sound`, e.g. `S(3) = 14`)
- Any finite Ramsey / hypergraph coloring problem in Lean 4's kernel (no `native_decide`).
-/

namespace HJBrigade

/-- Branching/witness DPLL reflection tree parameterized by witness descriptor type `W` and colors `r`. -/
inductive HyperCert (W : Type) (r : Nat) where
  | witness (w : W) (color : Nat)
  | split (v : Nat) (branches : List (HyperCert W r))

def assignHasVertex (v col : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (p, c) :: rest => ((p == v) && (c == col)) || assignHasVertex v col rest

def allVerticesColored (V col : Nat) (assign : List (Nat × Nat)) : List Nat → Bool
  | [] => true
  | v :: rest => decide (v < V) && assignHasVertex v col assign && allVerticesColored V col assign rest

mutual
  def checkHyperBranches {W : Type} (V r : Nat) (validW : W → Bool) (edgePts : W → List Nat)
      (v : Nat) (assign : List (Nat × Nat)) (colVal : Nat) : List (HyperCert W r) → Bool
    | [] => true
    | br :: rest =>
      checkHyperCert V r validW edgePts br ((v, colVal) :: assign) &&
      checkHyperBranches V r validW edgePts v assign (colVal + 1) rest

  def checkHyperCert {W : Type} (V r : Nat) (validW : W → Bool) (edgePts : W → List Nat) :
      HyperCert W r → List (Nat × Nat) → Bool
    | .witness w color, assign =>
      decide (color < r) &&
      validW w &&
      allVerticesColored V color assign (edgePts w)
    | .split v branches, assign =>
      decide (v < V) &&
      decide (branches.length = r) &&
      checkHyperBranches V r validW edgePts v assign 0 branches
end

private theorem assignHasVertex_sound {V r : Nat} (c : Fin V → Fin r)
    (assign : List (Nat × Nat))
    (hassign : ∀ p ∈ assign, ∃ hv : p.1 < V, (c ⟨p.1, hv⟩).val = p.2)
    (v col : Nat) (hv : v < V) (h : assignHasVertex v col assign = true) :
    (c ⟨v, hv⟩).val = col := by
  induction assign with
  | nil => simp [assignHasVertex] at h
  | cons hd tl ih =>
    rcases hd with ⟨p0, c0⟩
    simp only [assignHasVertex, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨hp, hc⟩ | htl
    · obtain ⟨hpv, hcv⟩ := hassign (p0, c0) List.mem_cons_self
      subst hp
      simpa [hc] using hcv
    · exact ih (fun p hp => hassign p (List.mem_cons_of_mem _ hp)) htl

private theorem allVerticesColored_sound {V r : Nat} (c : Fin V → Fin r)
    (assign : List (Nat × Nat))
    (hassign : ∀ p ∈ assign, ∃ hv : p.1 < V, (c ⟨p.1, hv⟩).val = p.2)
    (col : Nat) :
    ∀ vs : List Nat, allVerticesColored V col assign vs = true →
      ∀ v ∈ vs, ∃ hv : v < V, (c ⟨v, hv⟩).val = col
  | [], _, _, hmem => nomatch hmem
  | v0 :: vs, h, v, hmem => by
    simp only [allVerticesColored, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact ⟨h.1.1, assignHasVertex_sound c assign hassign v col h.1.1 h.1.2⟩
    · exact allVerticesColored_sound c assign hassign col vs h.2 v htail

private theorem nthHyperBranch_check {W : Type} {V r v : Nat}
    {validW : W → Bool} {edgePts : W → List Nat} :
    ∀ (branches : List (HyperCert W r)) (assign : List (Nat × Nat)) (base col : Nat),
      checkHyperBranches V r validW edgePts v assign base branches = true →
      col < branches.length →
      ∃ br, br ∈ branches ∧ checkHyperCert V r validW edgePts br ((v, base + col) :: assign) = true
  | [], _, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | br :: rest, assign, base, col, h, hlt => by
    simp only [checkHyperBranches, Bool.and_eq_true] at h
    cases col with
    | zero => exact ⟨br, List.mem_cons_self, by simpa using h.1⟩
    | succ col' =>
      obtain ⟨br', hmem, hbr'⟩ :=
        nthHyperBranch_check rest assign (base + 1) col' h.2 (Nat.lt_of_succ_lt_succ hlt)
      refine ⟨br', List.mem_cons_of_mem _ hmem, ?_⟩
      have hsum : base + 1 + col' = base + (col' + 1) := by omega
      rwa [hsum] at hbr'

private theorem sizeOf_lt_of_mem_hyperList {W : Type} {r : Nat} {br : HyperCert W r} :
    ∀ {bs : List (HyperCert W r)}, br ∈ bs → sizeOf br < sizeOf bs
  | _ :: _, .head _ => by simp +arith
  | _ :: _, .tail _ h => by
    have ih := sizeOf_lt_of_mem_hyperList h
    simp +arith
    omega

private theorem sizeOf_lt_hyperSplit {W : Type} {r v : Nat} {br : HyperCert W r}
    {branches : List (HyperCert W r)} (hmem : br ∈ branches) :
    sizeOf br < sizeOf (HyperCert.split v branches) := by
  have h1 := sizeOf_lt_of_mem_hyperList hmem
  simp +arith
  omega

private theorem checkHyperCert_eval {W : Type} (V r : Nat) (validW : W → Bool)
    (edgePts : W → List Nat) (c : Fin V → Fin r) :
    ∀ (tree : HyperCert W r) (assign : List (Nat × Nat)),
      checkHyperCert V r validW edgePts tree assign = true →
      (∀ p ∈ assign, ∃ hv : p.1 < V, (c ⟨p.1, hv⟩).val = p.2) →
      ∃ w : W, validW w = true ∧ ∃ col : Fin r, ∀ v ∈ edgePts w, ∃ hv : v < V, c ⟨v, hv⟩ = col
  | .witness w color, assign, h, hassign => by
    simp only [checkHyperCert, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hcol, hw⟩, hall⟩
    refine ⟨w, hw, ⟨color, hcol⟩, ?_⟩
    intro v hvMem
    obtain ⟨hv, hval⟩ := allVerticesColored_sound c assign hassign color (edgePts w) hall v hvMem
    exact ⟨hv, Fin.ext hval⟩
  | .split v branches, assign, h, hassign => by
    simp only [checkHyperCert, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hvV, hlen⟩, hbrs⟩
    let curCol := c ⟨v, hvV⟩
    have hlt : curCol.val < branches.length := Nat.lt_of_lt_of_eq curCol.isLt hlen.symm
    obtain ⟨br, hmem, hbr⟩ := nthHyperBranch_check branches assign 0 curCol.val hbrs hlt
    simp only [Nat.zero_add] at hbr
    have hdec : sizeOf br < sizeOf (HyperCert.split v branches) := sizeOf_lt_hyperSplit hmem
    refine checkHyperCert_eval V r validW edgePts c br ((v, curCol.val) :: assign) hbr ?_
    intro p hp
    cases hp with
    | head => exact ⟨hvV, rfl⟩
    | tail _ hmem' => exact hassign p hmem'
termination_by tree => sizeOf tree

/-- Unbroken hypergraph DPLL reflection soundness. -/
theorem checkHyperCert_sound {W : Type} (V r : Nat) (validW : W → Bool) (edgePts : W → List Nat)
    (tree : HyperCert W r) (h : checkHyperCert V r validW edgePts tree [] = true) :
    ∀ c : Fin V → Fin r,
      ∃ w : W, validW w = true ∧ ∃ col : Fin r, ∀ v ∈ edgePts w, ∃ hv : v < V, c ⟨v, hv⟩ = col :=
  fun c => checkHyperCert_eval V r validW edgePts c tree [] h (fun _ hp => nomatch hp)

/-- Color-permutation symmetry-broken hypergraph DPLL reflection soundness (fixing `rootV` to color `0`). -/
theorem checkHyperCertSym_sound {W : Type} (V r : Nat) (hr : r ≥ 1) (rootV : Nat)
    (hroot : rootV < V) (validW : W → Bool) (edgePts : W → List Nat)
    (tree : HyperCert W r) (h : checkHyperCert V r validW edgePts tree [(rootV, 0)] = true) :
    ∀ c : Fin V → Fin r,
      ∃ w : W, validW w = true ∧ ∃ col : Fin r, ∀ v ∈ edgePts w, ∃ hv : v < V, c ⟨v, hv⟩ = col := by
  intro c
  let a := c ⟨rootV, hroot⟩
  let cPerm : Fin V → Fin r := fun v => swapColor0 hr a (c v)
  have hrootVal : (cPerm ⟨rootV, hroot⟩).val = 0 := by
    change (swapColor0 hr a a).val = 0
    rw [swapColor0_self]
  obtain ⟨w, hw, col, hpts⟩ :=
    checkHyperCert_eval V r validW edgePts cPerm tree [(rootV, 0)] h (by
      intro p hp
      cases hp with
      | head => exact ⟨hroot, hrootVal⟩
      | tail _ hmem => nomatch hmem)
  refine ⟨w, hw, swapColor0 hr a col, ?_⟩
  intro v hvMem
  obtain ⟨hv, hcv⟩ := hpts v hvMem
  refine ⟨hv, ?_⟩
  calc
    c ⟨v, hv⟩ = swapColor0 hr a (cPerm ⟨v, hv⟩) := (swapColor0_invol hr a (c ⟨v, hv⟩)).symm
    _ = swapColor0 hr a col := congrArg (swapColor0 hr a) hcv

/-- Valid `k`-term arithmetic progression descriptor `(start, step)` in `{0, ..., N - 1}`. -/
def vdwValidAP (N k : Nat) (w : Nat × Nat) : Bool :=
  decide (w.2 ≥ 1 ∧ w.1 + (k - 1) * w.2 < N)

/-- Vertex list of a `k`-term arithmetic progression `(start, step)`. -/
def vdwAPPts (k : Nat) (w : Nat × Nat) : List Nat :=
  (List.range k).map (fun t => w.1 + t * w.2)

/-- Reflection checker certifying finite Van der Waerden upper bounds `HasMonoAP N k r`. -/
theorem checkVdWCertSym_sound (N k r : Nat) (hr : r ≥ 1) (rootV : Nat) (hroot : rootV < N)
    (tree : HyperCert (Nat × Nat) r)
    (h : checkHyperCert N r (vdwValidAP N k) (vdwAPPts k) tree [(rootV, 0)] = true) :
    HasMonoAP N k r := by
  intro f
  obtain ⟨⟨a, step⟩, hw, col, hpts⟩ :=
    checkHyperCertSym_sound N r hr rootV hroot (vdwValidAP N k) (vdwAPPts k) tree h f
  simp only [vdwValidAP, decide_eq_true_eq] at hw
  refine ⟨a, step, hw.1, hw.2, col, ?_⟩
  intro t
  have hmem : a + t.val * step ∈ vdwAPPts k (a, step) :=
    List.mem_map.mpr ⟨t.val, List.mem_range.mpr t.isLt, rfl⟩
  obtain ⟨hv, hcol⟩ := hpts (a + t.val * step) hmem
  exact hcol

end HJBrigade
