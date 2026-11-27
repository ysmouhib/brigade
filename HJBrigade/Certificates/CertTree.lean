import HJBrigade.Core.Line

/-!
# Verified Reflection Checker for Finite Hales–Jewett Upper-Bound Certificates

Certifies finite `HJUpper d k r` statements in Lean 4's kernel using a compact
branching/witness tree `CertTree r`, avoiding `native_decide` and avoiding `O(r^(k^d))`
naive quantification over all colorings.

Both `checkCert_sound` (general `r`) and `checkCertSym2_sound` (with `r = 2` color-flip
symmetry breaking) are formally proved against `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace HJBrigade

/-- Compact DPLL/branching certificate tree for `HJUpper d k r`. -/
inductive CertTree (r : Nat) where
  | witness (mask : List (Option Nat)) (color : Nat)
  | split (ptIdx : Nat) (branches : List (CertTree r))

/-- Decode a base-`k` integer index `idx` into `Word d k`. -/
def decodeWord (d k : Nat) (hk : k ≥ 1) (idx : Nat) : Word d k :=
  fun i => ⟨(idx / k ^ i.val) % k, Nat.mod_lt _ hk⟩

def maskHasWildcard : List (Option Nat) → Bool
  | [] => false
  | none :: _ => true
  | some _ :: rest => maskHasWildcard rest

def maskBoundsOk (k : Nat) : List (Option Nat) → Bool
  | [] => true
  | none :: rest => maskBoundsOk k rest
  | some a :: rest => decide (a < k) && maskBoundsOk k rest

def wordMatchesMaskAux (k tVal : Nat) (idx : Nat) : List (Option Nat) → Bool
  | [] => true
  | opt :: rest =>
    let expected := match opt with | none => tVal | some a => a
    (idx % k == expected) && wordMatchesMaskAux k tVal (idx / k) rest

def assignHasLinePoint (k tVal color : Nat) (mask : List (Option Nat)) : List (Nat × Nat) → Bool
  | [] => false
  | (ptIdx, col) :: rest =>
    ((col == color) && wordMatchesMaskAux k tVal ptIdx mask) ||
    assignHasLinePoint k tVal color mask rest

def checkAllLetters (k color : Nat) (mask : List (Option Nat)) (assign : List (Nat × Nat)) : Nat → Bool
  | 0 => true
  | n + 1 => assignHasLinePoint k n color mask assign && checkAllLetters k color mask assign n

mutual
  def checkCertBranches (d k r ptIdx : Nat) (assign : List (Nat × Nat)) (colVal : Nat) :
      List (CertTree r) → Bool
    | [] => true
    | br :: rest =>
      checkCert d k r br ((ptIdx, colVal) :: assign) &&
      checkCertBranches d k r ptIdx assign (colVal + 1) rest

  def checkCert (d k r : Nat) : CertTree r → List (Nat × Nat) → Bool
    | .witness mask color, assign =>
      decide (mask.length = d) &&
      decide (color < r) &&
      maskHasWildcard mask &&
      maskBoundsOk k mask &&
      checkAllLetters k color mask assign k
    | .split ptIdx branches, assign =>
      decide (branches.length = r) &&
      checkCertBranches d k r ptIdx assign 0 branches
end

def listGetOpt : List (Option Nat) → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => x
  | _ :: xs, n + 1 => listGetOpt xs n

private theorem maskHasWildcard_sound :
    ∀ (mask : List (Option Nat)),
      maskHasWildcard mask = true →
      ∃ n, n < mask.length ∧ listGetOpt mask n = none
  | [], h => by simp [maskHasWildcard] at h
  | none :: rest, _ => ⟨0, Nat.zero_lt_succ rest.length, rfl⟩
  | some _ :: rest, h => by
    simp only [maskHasWildcard] at h
    obtain ⟨n, hn, hget⟩ := maskHasWildcard_sound rest h
    exact ⟨n + 1, Nat.succ_lt_succ hn, hget⟩

private theorem maskBoundsOk_sound :
    ∀ (k : Nat) (mask : List (Option Nat)),
      maskBoundsOk k mask = true →
      ∀ n a, n < mask.length → listGetOpt mask n = some a → a < k
  | _, [], _ => fun _ _ hn => absurd hn (Nat.not_lt_zero _)
  | k, none :: rest, h => by
    simp only [maskBoundsOk] at h
    intro n a hn hget
    cases n with
    | zero => simp [listGetOpt] at hget
    | succ n' => exact maskBoundsOk_sound k rest h n' a (Nat.lt_of_succ_lt_succ hn) hget
  | k, some b :: rest, h => by
    simp only [maskBoundsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    intro n a hn hget
    cases n with
    | zero =>
      simp only [listGetOpt] at hget
      cases hget
      exact h.1
    | succ n' => exact maskBoundsOk_sound k rest h.2 n' a (Nat.lt_of_succ_lt_succ hn) hget

private theorem wordMatchesMaskAux_sound :
    ∀ (mask : List (Option Nat)) (k tVal idx : Nat),
      wordMatchesMaskAux k tVal idx mask = true →
      ∀ n, n < mask.length →
        (idx / k ^ n) % k = match listGetOpt mask n with | none => tVal | some a => a
  | [], _, _, _, _ => fun _ hn => absurd hn (Nat.not_lt_zero _)
  | opt :: rest, k, tVal, idx, h => by
    simp only [wordMatchesMaskAux, Bool.and_eq_true, beq_iff_eq] at h
    intro n hn
    cases n with
    | zero =>
      simpa [listGetOpt, Nat.pow_zero, Nat.div_one] using h.1
    | succ n' =>
      have ih := wordMatchesMaskAux_sound rest k tVal (idx / k) h.2 n' (Nat.lt_of_succ_lt_succ hn)
      have hpow : k ^ (n' + 1) = k * k ^ n' := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow, ← Nat.div_div_eq_div_mul]
      exact ih

def maskToFinMask (d k : Nat) (mask : List (Option Nat)) : Fin d → Option (Fin k) :=
  fun i =>
    match listGetOpt mask i.val with
    | none => none
    | some a => if ha : a < k then some ⟨a, ha⟩ else none

private theorem maskToFinMask_none (d k : Nat) (mask : List (Option Nat)) (i : Fin d)
    (h : listGetOpt mask i.val = none) :
    maskToFinMask d k mask i = none := by
  simp [maskToFinMask, h]

private theorem evalMask_from_wordMatches (d k : Nat) (hk : k ≥ 1)
    (mask : List (Option Nat)) (hlen : mask.length = d) (hb : maskBoundsOk k mask = true)
    (t : Fin k) (ptIdx : Nat) (hm : wordMatchesMaskAux k t.val ptIdx mask = true) :
    decodeWord d k hk ptIdx = evalMask (maskToFinMask d k mask) t := by
  funext i
  apply Fin.ext
  have hmod := wordMatchesMaskAux_sound mask k t.val ptIdx hm i.val (hlen ▸ i.isLt)
  change (ptIdx / k ^ i.val) % k = ((maskToFinMask d k mask i).getD t).val
  dsimp [maskToFinMask]
  cases h : listGetOpt mask i.val with
  | none =>
    simp only [h] at hmod
    simpa using hmod
  | some a =>
    have ha : a < k := maskBoundsOk_sound k mask hb i.val a (hlen ▸ i.isLt) h
    simp only [h] at hmod
    simp [ha, hmod]

private theorem assignHasLinePoint_sound {d k r : Nat} (hk : k ≥ 1)
    (c : Word d k → Fin r) (assign : List (Nat × Nat))
    (hassign : ∀ p ∈ assign, (c (decodeWord d k hk p.1)).val = p.2)
    (mask : List (Option Nat)) (hlen : mask.length = d) (hb : maskBoundsOk k mask = true)
    (color : Nat) (t : Fin k)
    (h : assignHasLinePoint k t.val color mask assign = true) :
    (c (evalMask (maskToFinMask d k mask) t)).val = color := by
  induction assign with
  | nil => simp [assignHasLinePoint] at h
  | cons hd tl ih =>
    rcases hd with ⟨ptIdx, col⟩
    simp only [assignHasLinePoint, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨hcol, hmatch⟩ | htl
    · have hc := hassign (ptIdx, col) List.mem_cons_self
      have heq := evalMask_from_wordMatches d k hk mask hlen hb t ptIdx hmatch
      rw [← heq, hc, hcol]
    · exact ih (fun p hp => hassign p (List.mem_cons_of_mem _ hp)) htl

private theorem checkAllLetters_sound {d k r : Nat} (hk : k ≥ 1)
    (c : Word d k → Fin r) (assign : List (Nat × Nat))
    (hassign : ∀ p ∈ assign, (c (decodeWord d k hk p.1)).val = p.2)
    (mask : List (Option Nat)) (hlen : mask.length = d) (hb : maskBoundsOk k mask = true)
    (color : Nat) :
    ∀ n : Nat, checkAllLetters k color mask assign n = true →
      ∀ (t : Fin k), t.val < n →
        (c (evalMask (maskToFinMask d k mask) t)).val = color
  | 0, _, _, ht => absurd ht (Nat.not_lt_zero _)
  | n + 1, h, t, ht => by
    simp only [checkAllLetters, Bool.and_eq_true] at h
    by_cases htn : t.val = n
    · exact assignHasLinePoint_sound hk c assign hassign mask hlen hb color t
        (by rw [htn]; exact h.1)
    · exact checkAllLetters_sound hk c assign hassign mask hlen hb color n h.2 t (by omega)

private theorem nthBranch_check {d k r ptIdx : Nat} :
    ∀ (branches : List (CertTree r)) (assign : List (Nat × Nat)) (base col : Nat),
      checkCertBranches d k r ptIdx assign base branches = true →
      col < branches.length →
      ∃ br, br ∈ branches ∧ checkCert d k r br ((ptIdx, base + col) :: assign) = true
  | [], _, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | br :: rest, assign, base, col, h, hlt => by
    simp only [checkCertBranches, Bool.and_eq_true] at h
    cases col with
    | zero => exact ⟨br, List.mem_cons_self, by simpa using h.1⟩
    | succ col' =>
      obtain ⟨br', hmem, hbr'⟩ := nthBranch_check rest assign (base + 1) col' h.2 (Nat.lt_of_succ_lt_succ hlt)
      refine ⟨br', List.mem_cons_of_mem _ hmem, ?_⟩
      have hsum : base + 1 + col' = base + (col' + 1) := by omega
      rwa [hsum] at hbr'

private theorem sizeOf_lt_of_mem_list {r : Nat} {br : CertTree r} :
    ∀ {bs : List (CertTree r)}, br ∈ bs → sizeOf br < sizeOf bs
  | _ :: _, .head _ => by simp +arith
  | _ :: _, .tail _ h => by
    have ih := sizeOf_lt_of_mem_list h
    simp +arith
    omega

private theorem sizeOf_lt_split {r : Nat} {ptIdx : Nat} {br : CertTree r}
    {branches : List (CertTree r)} (hmem : br ∈ branches) :
    sizeOf br < sizeOf (CertTree.split ptIdx branches) := by
  have h1 := sizeOf_lt_of_mem_list hmem
  simp +arith
  omega

private theorem checkCert_eval (d k r : Nat) (hk : k ≥ 1) (c : Word d k → Fin r) :
    ∀ (tree : CertTree r) (assign : List (Nat × Nat)),
      checkCert d k r tree assign = true →
      (∀ p ∈ assign, (c (decodeWord d k hk p.1)).val = p.2) →
      HasMonoLine d k r c
  | .witness mask color, assign, h, hassign => by
    simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨hlen, hcol⟩, hwild⟩, hbounds⟩, hletters⟩
    have hmaskWild : ∃ i : Fin d, maskToFinMask d k mask i = none := by
      obtain ⟨n, hn, hget⟩ := maskHasWildcard_sound mask hwild
      exact ⟨⟨n, hlen ▸ hn⟩, maskToFinMask_none d k mask ⟨n, hlen ▸ hn⟩ hget⟩
    let L : Line d k := ⟨maskToFinMask d k mask, hmaskWild⟩
    refine ⟨L, ⟨color, hcol⟩, ?_⟩
    intro t
    have hval := checkAllLetters_sound hk c assign hassign mask hlen hbounds color k hletters t t.isLt
    exact Fin.ext hval
  | .split ptIdx branches, assign, h, hassign => by
    simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hlen, hbrs⟩
    let curCol := c (decodeWord d k hk ptIdx)
    have hlt : curCol.val < branches.length := Nat.lt_of_lt_of_eq curCol.isLt hlen.symm
    obtain ⟨br, hmem, hbr⟩ := nthBranch_check branches assign 0 curCol.val hbrs hlt
    simp only [Nat.zero_add] at hbr
    have hdec : sizeOf br < sizeOf (CertTree.split ptIdx branches) := sizeOf_lt_split hmem
    refine checkCert_eval d k r hk c br ((ptIdx, curCol.val) :: assign) hbr ?_
    intro p hp
    cases hp with
    | head => rfl
    | tail _ hmem' => exact hassign p hmem'
termination_by tree => sizeOf tree

/-- Soundness of general DPLL certificate trees for `HJUpper d k r`. -/
theorem checkCert_sound (d k r : Nat) (hk : k ≥ 1) (tree : CertTree r)
    (h : checkCert d k r tree [] = true) : HJUpper d k r := by
  intro c
  exact checkCert_eval d k r hk c tree [] h (fun _ hp => nomatch hp)

/-- Soundness of 2-color symmetry-broken certificate trees (fixing `rootIdx` to color `0`). -/
theorem checkCertSym2_sound (d k : Nat) (hk : k ≥ 1) (rootIdx : Nat) (tree : CertTree 2)
    (h : checkCert d k 2 tree [(rootIdx, 0)] = true) : HJUpper d k 2 := by
  intro c
  let c0 := c (decodeWord d k hk rootIdx)
  match hc0 : c0.val with
  | 0 =>
    refine checkCert_eval d k 2 hk c tree [(rootIdx, 0)] h ?_
    intro p hp
    cases hp with
    | head => exact hc0
    | tail _ hmem => nomatch hmem
  | 1 =>
    let cFlip : Word d k → Fin 2 := fun w => ⟨1 - (c w).val, by omega⟩
    have hflipRoot : (cFlip (decodeWord d k hk rootIdx)).val = 0 := by
      change 1 - c0.val = 0
      omega
    obtain ⟨L, col, hL⟩ := checkCert_eval d k 2 hk cFlip tree [(rootIdx, 0)] h (by
      intro p hp
      cases hp with
      | head => exact hflipRoot
      | tail _ hmem => nomatch hmem)
    refine ⟨L, ⟨1 - col.val, by omega⟩, ?_⟩
    intro t
    have hval := congrArg Fin.val (hL t)
    change 1 - (c (L.eval t)).val = col.val at hval
    have hbound : (c (L.eval t)).val < 2 := (c (L.eval t)).isLt
    exact Fin.ext (by dsimp; omega)
  | _ + 2 =>
    have hlt := c0.isLt
    omega

def swapColor0 {r : Nat} (hr : r ≥ 1) (a x : Fin r) : Fin r :=
  if x = a then ⟨0, hr⟩
  else if x.val = 0 then a
  else x

theorem swapColor0_self {r : Nat} (hr : r ≥ 1) (a : Fin r) :
    swapColor0 hr a a = ⟨0, hr⟩ := by
  simp [swapColor0]

theorem swapColor0_invol {r : Nat} (hr : r ≥ 1) (a x : Fin r) :
    swapColor0 hr a (swapColor0 hr a x) = x := by
  by_cases hxa : x = a
  · subst hxa
    rw [swapColor0_self]
    by_cases ha0 : (⟨0, hr⟩ : Fin r) = x
    · simp [swapColor0, ha0]
    · simp [swapColor0, ha0]
  · by_cases hx0 : x.val = 0
    · have hfx : swapColor0 hr a x = a := by simp [swapColor0, hxa, hx0]
      rw [hfx, swapColor0_self]
      exact Fin.ext hx0.symm
    · have hfx : swapColor0 hr a x = x := by simp [swapColor0, hxa, hx0]
      rw [hfx, hfx]

/-- General `r`-color symmetry-broken certificate soundness: fixing `rootIdx` to color `0`
via color permutation `swapColor0` proves `HJUpper d k r` for any `r ≥ 1`. -/
theorem checkCertSym_sound (d k r : Nat) (hk : k ≥ 1) (hr : r ≥ 1)
    (rootIdx : Nat) (tree : CertTree r)
    (h : checkCert d k r tree [(rootIdx, 0)] = true) : HJUpper d k r := by
  intro c
  let a := c (decodeWord d k hk rootIdx)
  let cPerm : Word d k → Fin r := fun w => swapColor0 hr a (c w)
  have hroot : (cPerm (decodeWord d k hk rootIdx)).val = 0 := by
    change (swapColor0 hr a a).val = 0
    rw [swapColor0_self]
  obtain ⟨L, col, hL⟩ := checkCert_eval d k r hk cPerm tree [(rootIdx, 0)] h (by
    intro p hp
    cases hp with
    | head => exact hroot
    | tail _ hmem => nomatch hmem)
  refine ⟨L, swapColor0 hr a col, ?_⟩
  intro t
  calc
    c (L.eval t) = swapColor0 hr a (cPerm (L.eval t)) := (swapColor0_invol hr a (c (L.eval t))).symm
    _ = swapColor0 hr a col := congrArg (swapColor0 hr a) (hL t)

end HJBrigade
