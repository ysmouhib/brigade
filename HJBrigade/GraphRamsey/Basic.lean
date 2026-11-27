import HJBrigade.Density.Sperner

/-!
# Graph & Multicolor Ramsey Theory (`GraphRamseyUpper`, Erdős–Szekeres, Greenwood–Gleason)

Formalizes finite 2-color and `r`-color graph Ramsey numbers cleanly in standalone Lean 4:
- `GraphRamseyUpper N s t`, `MulticolorRamseyUpper N r k`
- `erdos_szekeres_step`, `erdos_szekeres`, and unconditional `graph_ramsey`
- `handshaking_even` & Greenwood–Gleason parity tightening `erdos_szekeres_even`
- `ramsey_triangle_step` (`R_{r+1}(3) ≤ r * (R_r(3) - 1) + 2`) & unconditional `multicolor_triangle_ramsey`
- Fast branch-and-pruning clique-absence checkers `checkNoClique_sound` and `checkNoMonoClique_sound`
-/

namespace HJBrigade

/-- Strictly increasing index embedding `Fin s → Fin N`. -/
def StrictMonoFin {s N : Nat} (f : Fin s → Fin N) : Prop :=
  ∀ i j : Fin s, i.val < j.val → (f i).val < (f j).val

theorem StrictMonoFin.inj {s N : Nat} {f : Fin s → Fin N} (hf : StrictMonoFin f)
    {i j : Fin s} (h : f i = f j) : i = j := by
  have hv : (f i).val = (f j).val := congrArg Fin.val h
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact absurd hv (Nat.ne_of_lt (hf i j hlt))
  · exact Fin.ext heq
  · exact absurd hv.symm (Nat.ne_of_lt (hf j i hgt))

theorem StrictMonoFin.comp {s M N : Nat} {f : Fin s → Fin M} {g : Fin M → Fin N}
    (hf : StrictMonoFin f) (hg : StrictMonoFin g) : StrictMonoFin (fun i => g (f i)) :=
  fun i j hij => hg (f i) (f j) (hf i j hij)

/-- `f` picks a monochromatic `Bool`-clique of color `col` inside `G`. -/
def IsBoolClique {N s : Nat} (G : Fin N → Fin N → Bool) (col : Bool) (f : Fin s → Fin N) : Prop :=
  StrictMonoFin f ∧ ∀ i j : Fin s, i.val < j.val → G (f i) (f j) = col

/-- Every 2-coloring of the upper pairs of `Fin N` has a `false`-`K_s` or a `true`-`K_t`. -/
def GraphRamseyUpper (N s t : Nat) : Prop :=
  ∀ G : Fin N → Fin N → Bool,
    (∃ f : Fin s → Fin N, IsBoolClique G false f) ∨
    (∃ g : Fin t → Fin N, IsBoolClique G true g)

/-- `f` picks a monochromatic `k`-clique of color `col : Fin r` inside `c`. -/
def IsMonoClique {N r k : Nat} (c : Fin N → Fin N → Fin r) (col : Fin r) (f : Fin k → Fin N) : Prop :=
  StrictMonoFin f ∧ ∀ i j : Fin k, i.val < j.val → c (f i) (f j) = col

/-- Every `r`-coloring of pairs of `Fin N` contains a monochromatic `K_k`. -/
def MulticolorRamseyUpper (N r k : Nat) : Prop :=
  ∀ c : Fin N → Fin N → Fin r, ∃ (col : Fin r) (f : Fin k → Fin N), IsMonoClique c col f

theorem GraphRamseyUpper.symm {N s t : Nat} (h : GraphRamseyUpper N s t) :
    GraphRamseyUpper N t s := by
  intro G
  rcases h (fun u v => !(G u v)) with ⟨f, hf, hfc⟩ | ⟨g, hg, hgc⟩
  · right
    refine ⟨f, hf, fun i j hij => ?_⟩
    have := hfc i j hij
    cases hG : G (f i) (f j) <;> simp_all
  · left
    refine ⟨g, hg, fun i j hij => ?_⟩
    have := hgc i j hij
    cases hG : G (g i) (g j) <;> simp_all

theorem GraphRamseyUpper.mono_N {N N' s t : Nat} (hle : N ≤ N') (h : GraphRamseyUpper N s t) :
    GraphRamseyUpper N' s t := by
  intro G
  let G' : Fin N → Fin N → Bool :=
    fun u v => G ⟨u.val, Nat.lt_of_lt_of_le u.isLt hle⟩ ⟨v.val, Nat.lt_of_lt_of_le v.isLt hle⟩
  let lift : Fin N → Fin N' := fun u => ⟨u.val, Nat.lt_of_lt_of_le u.isLt hle⟩
  have hlift : StrictMonoFin lift := fun _ _ hij => hij
  rcases h G' with ⟨f, hf, hfc⟩ | ⟨g, hg, hgc⟩
  · left
    exact ⟨fun i => lift (f i), hf.comp hlift, hfc⟩
  · right
    exact ⟨fun i => lift (g i), hg.comp hlift, hgc⟩

theorem ramsey_left_one (N t : Nat) (hN : N ≥ 1) : GraphRamseyUpper N 1 t := by
  intro _
  left
  refine ⟨fun _ => ⟨0, hN⟩, fun i j hij => ?_, fun i j hij => ?_⟩
  · have := i.isLt; have := j.isLt; omega
  · have := i.isLt; have := j.isLt; omega

theorem ramsey_right_one (N s : Nat) (hN : N ≥ 1) : GraphRamseyUpper N s 1 :=
  (ramsey_left_one N s hN).symm

theorem ramsey_left_two (t : Nat) (_ht : t ≥ 1) : GraphRamseyUpper t 2 t := by
  intro G
  by_cases hex : ∃ i j : Fin t, i.val < j.val ∧ G i j = false
  · left
    obtain ⟨i, j, hij, hG⟩ := hex
    refine ⟨fun x => if x.val = 0 then i else j, ?_, ?_⟩
    · intro a b hab
      have := a.isLt; have := b.isLt
      have ha0 : a.val = 0 := by omega
      have hb1 : b.val = 1 := by omega
      simp [ha0, hb1, hij]
    · intro a b hab
      have := a.isLt; have := b.isLt
      have ha0 : a.val = 0 := by omega
      have hb1 : b.val = 1 := by omega
      simp [ha0, hb1, hG]
  · right
    refine ⟨id, fun _ _ hij => hij, fun i j hij => ?_⟩
    cases hG : G i j with
    | true => exact hG
    | false => exact absurd ⟨i, j, hij, hG⟩ hex

theorem ramsey_right_two (s : Nat) (hs : s ≥ 1) : GraphRamseyUpper s s 2 :=
  (ramsey_left_two s hs).symm

/-- Order-preserving subset extraction: if at least `M` elements satisfy `P`, there is a
strictly monotone embedding `Fin M → Fin N` into the true elements of `P`. -/
theorem embed_of_card_ge :
    ∀ {N M : Nat} (P : Fin N → Bool),
      M ≤ sumFin N (fun v => if P v then 1 else 0) →
      ∃ emb : Fin M → Fin N, StrictMonoFin emb ∧ ∀ i : Fin M, P (emb i) = true
  | 0, 0, _, _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | 0, _ + 1, _, hle => by
    simp [sumFin] at hle
  | N + 1, 0, _, _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | N + 1, M + 1, P, hle => by
    let Ptail : Fin N → Bool := fun v => P ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩
    have hsum : sumFin (N + 1) (fun v => if P v then 1 else 0) =
        (if P ⟨0, Nat.zero_lt_succ N⟩ then 1 else 0) +
          sumFin N (fun v => if Ptail v then 1 else 0) := rfl
    rw [hsum] at hle
    cases hP0 : P ⟨0, Nat.zero_lt_succ N⟩ with
    | false =>
      simp only [hP0, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hle
      obtain ⟨emb', hmono', hP'⟩ := embed_of_card_ge Ptail hle
      refine ⟨fun i => ⟨(emb' i).val + 1, Nat.succ_lt_succ (emb' i).isLt⟩, ?_, ?_⟩
      · intro i j hij
        exact Nat.succ_lt_succ (hmono' i j hij)
      · intro i
        exact hP' i
    | true =>
      simp only [hP0, ↓reduceIte] at hle
      have htail : M ≤ sumFin N (fun v => if Ptail v then 1 else 0) := by omega
      obtain ⟨emb', hmono', hP'⟩ := embed_of_card_ge Ptail htail
      refine ⟨consFin ⟨0, Nat.zero_lt_succ N⟩
          (fun i => ⟨(emb' i).val + 1, Nat.succ_lt_succ (emb' i).isLt⟩), ?_, ?_⟩
      · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
        dsimp only at hab
        cases a with
        | zero =>
          cases b with
          | zero => omega
          | succ b' =>
            dsimp [consFin]
            exact Nat.zero_lt_succ _
        | succ a' =>
          cases b with
          | zero => omega
          | succ b' =>
            dsimp [consFin]
            exact Nat.succ_lt_succ (hmono' _ _ (Nat.lt_of_succ_lt_succ hab))
      · intro ⟨a, ha⟩
        cases a with
        | zero => exact hP0
        | succ a' => exact hP' ⟨a', Nat.lt_of_succ_lt_succ ha⟩

private theorem sumFin_erase_one :
    ∀ {N : Nat} (v0 : Fin N) (Q : Fin N → Bool), Q v0 = true →
      sumFin N (fun v => if Q v then 1 else 0) =
      1 + sumFin N (fun v => if (Q v && decide (v ≠ v0)) then 1 else 0)
  | 0, v0, _, _ => v0.elim0
  | N + 1, ⟨vv, hvv⟩, Q, hQ0 => by
    let Qt : Fin N → Bool := fun v => Q ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩
    cases vv with
    | zero =>
      have hhead : Q ⟨0, Nat.zero_lt_succ N⟩ = true := hQ0
      have htmatch : (fun v : Fin N =>
          if (Q ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ &&
              decide ((⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ : Fin (N + 1)) ≠ ⟨0, hvv⟩)) then 1 else 0) =
          (fun v : Fin N => if Qt v then 1 else 0) := by
        funext v
        simp [Qt]
      have h0f : decide ((⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1)) ≠ ⟨0, hvv⟩) = false := by
        simp
      dsimp only [sumFin]
      rw [htmatch, h0f]
      change (if Q ⟨0, Nat.zero_lt_succ N⟩ = true then 1 else 0) +
          sumFin N (fun v => if Qt v = true then 1 else 0) =
        1 + ((if (Q ⟨0, Nat.zero_lt_succ N⟩ && false) = true then 1 else 0) +
          sumFin N (fun v => if Qt v = true then 1 else 0))
      rw [hhead]
      simp
    | succ vv' =>
      have hne0 : (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1)) ≠ ⟨vv' + 1, hvv⟩ := by
        intro h
        have := congrArg Fin.val h
        dsimp only at this
        omega
      let v0' : Fin N := ⟨vv', Nat.lt_of_succ_lt_succ hvv⟩
      have ih := sumFin_erase_one v0' Qt hQ0
      have htmatch : (fun v : Fin N =>
          if (Q ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ &&
              decide ((⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ : Fin (N + 1)) ≠ ⟨vv' + 1, hvv⟩)) then 1 else 0) =
          (fun v : Fin N => if (Qt v && decide (v ≠ v0')) then 1 else 0) := by
        funext v
        by_cases hv : v = v0'
        · have hv' : (⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ : Fin (N + 1)) = ⟨vv' + 1, hvv⟩ := by
            apply Fin.ext
            have := congrArg Fin.val hv
            dsimp [v0'] at this ⊢
            omega
          rw [hv', hv]
          simp
        · have hv' : (⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ : Fin (N + 1)) ≠ ⟨vv' + 1, hvv⟩ := by
            intro h
            apply hv
            apply Fin.ext
            have := congrArg Fin.val h
            dsimp [v0'] at this ⊢
            omega
          rw [decide_eq_true hv, decide_eq_true hv']
      dsimp only [sumFin]
      rw [htmatch]
      have h0d : decide ((⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1)) ≠ ⟨vv' + 1, hvv⟩) = true :=
        decide_eq_true hne0
      change (if Q ⟨0, Nat.zero_lt_succ N⟩ = true then 1 else 0) +
          sumFin N (fun v => if Qt v = true then 1 else 0) =
        1 + ((if (Q ⟨0, Nat.zero_lt_succ N⟩ &&
              decide ((⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1)) ≠ ⟨vv' + 1, hvv⟩)) = true then 1 else 0) +
          sumFin N (fun v => if (Qt v && decide (v ≠ v0')) = true then 1 else 0))
      rw [h0d, Bool.and_true, ih]
      omega

private theorem card_ge_of_inj :
    ∀ {s N : Nat} (g : Fin s → Fin N) (Q : Fin N → Bool),
      (∀ i j : Fin s, g i = g j → i = j) →
      (∀ i : Fin s, Q (g i) = true) →
      s ≤ sumFin N (fun v => if Q v then 1 else 0)
  | 0, _, _, _, _, _ => Nat.zero_le _
  | s + 1, N, g, Q, hinj, hQ => by
    let v0 := g ⟨0, Nat.zero_lt_succ s⟩
    have herase := sumFin_erase_one v0 Q (hQ ⟨0, Nat.zero_lt_succ s⟩)
    let gTail : Fin s → Fin N := fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    have hinjTail : ∀ i j : Fin s, gTail i = gTail j → i = j := fun i j h => by
      have := hinj _ _ h
      apply Fin.ext
      have := congrArg Fin.val this
      dsimp at this ⊢
      omega
    let Q' : Fin N → Bool := fun v => Q v && decide (v ≠ v0)
    have hQ' : ∀ i : Fin s, Q' (gTail i) = true := fun i => by
      have hne : gTail i ≠ v0 := fun h => by
        have := hinj ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⟨0, Nat.zero_lt_succ s⟩ h
        have := congrArg Fin.val this
        dsimp only at this
        omega
      have hiQ : Q (gTail i) = true := hQ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      simp [Q', hiQ, hne]
    have ih := card_ge_of_inj gTail Q' hinjTail hQ'
    dsimp only [Q'] at ih
    omega

/-- Upper-triangle symmetrization of a graph predicate `G`. -/
def symGraph {N : Nat} (G : Fin N → Fin N → Bool) (u v : Fin N) : Bool :=
  if u.val < v.val then G u v else if v.val < u.val then G v u else false

theorem symGraph_comm {N : Nat} (G : Fin N → Fin N → Bool) (u v : Fin N) :
    symGraph G u v = symGraph G v u := by
  dsimp only [symGraph]
  rcases Nat.lt_trichotomy u.val v.val with h | h | h
  · have hnot : ¬ (v.val < u.val) := by omega
    simp [h, hnot]
  · simp [h]
  · have hnot : ¬ (u.val < v.val) := by omega
    simp [h, hnot]

private theorem isBoolClique_symGraph_iff {N s : Nat} (G : Fin N → Fin N → Bool) (col : Bool)
    (f : Fin s → Fin N) :
    IsBoolClique (symGraph G) col f ↔ IsBoolClique G col f := by
  constructor
  · rintro ⟨hf, hfc⟩
    refine ⟨hf, fun i j hij => ?_⟩
    have hval := hf i j hij
    simpa [symGraph, hval] using hfc i j hij
  · rintro ⟨hf, hfc⟩
    refine ⟨hf, fun i j hij => ?_⟩
    have hval := hf i j hij
    simpa [symGraph, hval] using hfc i j hij

private theorem clique_extend_with_hub {N s : Nat} (G : Fin N → Fin N → Bool) (col : Bool)
    (u0 : Fin N) (f : Fin s → Fin N) (hf : IsBoolClique G col f)
    (hdiff : ∀ i : Fin s, f i ≠ u0) (hadj : ∀ i : Fin s, symGraph G u0 (f i) = col) :
    ∃ f' : Fin (s + 1) → Fin N, IsBoolClique G col f' := by
  let g : Fin (s + 1) → Fin N := consFin u0 f
  have hinj : ∀ i j : Fin (s + 1), g i = g j → i = j := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h
    cases a with
    | zero =>
      cases b with
      | zero => rfl
      | succ b' => exact absurd h.symm (hdiff ⟨b', Nat.lt_of_succ_lt_succ hb⟩)
    | succ a' =>
      cases b with
      | zero => exact absurd h (hdiff ⟨a', Nat.lt_of_succ_lt_succ ha⟩)
      | succ b' =>
        have hfeq : f ⟨a', Nat.lt_of_succ_lt_succ ha⟩ = f ⟨b', Nat.lt_of_succ_lt_succ hb⟩ := h
        have hij := hf.1.inj hfeq
        have hval := congrArg Fin.val hij
        dsimp only at hval
        apply Fin.ext
        dsimp only
        omega
  letI : ∀ v : Fin N, Decidable (v = u0 ∨ ∃ i : Fin s, f i = v) :=
    fun v => instDecidableOr
  let Q : Fin N → Bool := fun v => decide (v = u0 ∨ ∃ i : Fin s, f i = v)
  have hQ : ∀ i : Fin (s + 1), Q (g i) = true := by
    intro ⟨a, ha⟩
    cases a with
    | zero =>
      simp only [Q, g, decide_eq_true_eq]
      exact Or.inl rfl
    | succ a' =>
      simp only [Q, g, consFin, decide_eq_true_eq]
      exact Or.inr ⟨⟨a', Nat.lt_of_succ_lt_succ ha⟩, rfl⟩
  have hcard := card_ge_of_inj g Q hinj hQ
  obtain ⟨f', hfMono, hfQ⟩ := embed_of_card_ge Q hcard
  have hSym : IsBoolClique (symGraph G) col f' := by
    refine ⟨hfMono, fun i j hij => ?_⟩
    have hne : f' i ≠ f' j := fun h => by
      have := hfMono i j hij
      rw [h] at this
      exact Nat.lt_irrefl _ this
    have hiQ : f' i = u0 ∨ ∃ a : Fin s, f a = f' i := by simpa [Q] using hfQ i
    have hjQ : f' j = u0 ∨ ∃ b : Fin s, f b = f' j := by simpa [Q] using hfQ j
    rcases hiQ with hi0 | ⟨a, ha⟩
    · rcases hjQ with hj0 | ⟨b, hb⟩
      · exact absurd (hi0.trans hj0.symm) hne
      · rw [hi0, ← hb]
        exact hadj b
    · rcases hjQ with hj0 | ⟨b, hb⟩
      · rw [hj0, ← ha, symGraph_comm]
        exact hadj a
      · rw [← ha, ← hb]
        rcases Nat.lt_trichotomy a.val b.val with hlt | heq | hgt
        · exact ((isBoolClique_symGraph_iff G col f).mpr hf).2 a b hlt
        · have hab_eq : a = b := Fin.ext heq
          rw [hab_eq] at ha
          exact absurd (ha.symm.trans hb) hne
        · rw [symGraph_comm]
          exact ((isBoolClique_symGraph_iff G col f).mpr hf).2 b a hgt
  exact ⟨f', (isBoolClique_symGraph_iff G col f').mp hSym⟩

private theorem degree_split_pivot {N M1 M2 : Nat} (G : Fin N → Fin N → Bool) (u0 : Fin N)
    (hge : M1 + M2 ≤ sumFin N (fun v => if u0 = v then 0 else 1)) :
    M1 ≤ sumFin N (fun v => if (decide (v ≠ u0) && !(symGraph G u0 v)) then 1 else 0) ∨
    M2 ≤ sumFin N (fun v => if (decide (v ≠ u0) && symGraph G u0 v) then 1 else 0) := by
  have hadd := sumFin_add N
    (fun v => if (decide (v ≠ u0) && !(symGraph G u0 v)) then 1 else 0)
    (fun v => if (decide (v ≠ u0) && symGraph G u0 v) then 1 else 0)
  have heq : (fun v : Fin N =>
      (if (decide (v ≠ u0) && !(symGraph G u0 v)) then 1 else 0) +
      (if (decide (v ≠ u0) && symGraph G u0 v) then 1 else 0)) =
      (fun v : Fin N => if u0 = v then 0 else 1) := by
    funext v
    by_cases hv : v = u0
    · simp [hv]
    · have hvu : ¬ (u0 = v) := fun h => hv h.symm
      cases symGraph G u0 v <;> simp [hv, hvu]
  rw [heq] at hadd
  rw [hadd] at hge
  omega

private theorem sumFin_ne_self :
    ∀ (N : Nat) (u0 : Fin N), sumFin N (fun v => if u0 = v then 0 else 1) + 1 = N
  | 0, u0 => u0.elim0
  | N + 1, ⟨uv, huv⟩ => by
    cases uv with
    | zero =>
      have ht : (fun v : Fin N => if (⟨0, huv⟩ : Fin (N + 1)) = ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ then 0 else 1) =
          (fun _ : Fin N => 1) := by
        funext v
        have hne : (⟨0, huv⟩ : Fin (N + 1)) ≠ ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ := by
          intro h
          have := congrArg Fin.val h
          dsimp only at this
          omega
        simp
      dsimp only [sumFin]
      rw [ht, sumFin_const]
      have hself0 : (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1)) = ⟨0, huv⟩ := rfl
      simp [hself0]
    | succ uv' =>
      have hne0 : (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1)) ≠ ⟨uv' + 1, huv⟩ := by
        intro h
        have := congrArg Fin.val h
        dsimp only at this
        omega
      let u0' : Fin N := ⟨uv', Nat.lt_of_succ_lt_succ huv⟩
      have ih := sumFin_ne_self N u0'
      have ht : (fun v : Fin N => if (⟨uv' + 1, huv⟩ : Fin (N + 1)) = ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ then 0 else 1) =
          (fun v : Fin N => if u0' = v then 0 else 1) := by
        funext v
        by_cases hv : u0' = v
        · have hv' : (⟨uv' + 1, huv⟩ : Fin (N + 1)) = ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ := by
            apply Fin.ext
            have := congrArg Fin.val hv
            dsimp [u0'] at this ⊢
            omega
          simp [hv, hv']
        · have hv' : (⟨uv' + 1, huv⟩ : Fin (N + 1)) ≠ ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ := by
            intro h
            apply hv
            apply Fin.ext
            have := congrArg Fin.val h
            dsimp [u0'] at this ⊢
            omega
          simp [hv, hv']
      have hne0' : (⟨uv' + 1, huv⟩ : Fin (N + 1)) ≠ ⟨0, Nat.zero_lt_succ N⟩ := fun h => hne0 h.symm
      dsimp only [sumFin]
      rw [ht]
      simp only [hne0', ↓reduceIte]
      omega

private theorem extend_from_pivot {N M1 M2 s t : Nat} (G : Fin N → Fin N → Bool) (u0 : Fin N)
    (h1 : GraphRamseyUpper M1 s (t + 1)) (h2 : GraphRamseyUpper M2 (s + 1) t)
    (hdeg : M1 ≤ sumFin N (fun v => if (decide (v ≠ u0) && !(symGraph G u0 v)) then 1 else 0) ∨
            M2 ≤ sumFin N (fun v => if (decide (v ≠ u0) && symGraph G u0 v) then 1 else 0)) :
    (∃ f : Fin (s + 1) → Fin N, IsBoolClique G false f) ∨
    (∃ g : Fin (t + 1) → Fin N, IsBoolClique G true g) := by
  rcases hdeg with hF | hT
  · let PF : Fin N → Bool := fun v => decide (v ≠ u0) && !(symGraph G u0 v)
    obtain ⟨emb, hmono, hPF⟩ := embed_of_card_ge PF hF
    let Gsub : Fin M1 → Fin M1 → Bool := fun a b => G (emb a) (emb b)
    rcases h1 Gsub with ⟨f, hf, hfc⟩ | ⟨g, hg, hgc⟩
    · left
      have hf' : IsBoolClique G false (fun i => emb (f i)) := ⟨hf.comp hmono, hfc⟩
      refine clique_extend_with_hub G false u0 _ hf' ?_ ?_
      · intro i
        have := hPF (f i)
        simp [PF] at this
        exact this.1
      · intro i
        have := hPF (f i)
        simp [PF] at this
        exact this.2
    · right
      exact ⟨fun i => emb (g i), hg.comp hmono, hgc⟩
  · let PT : Fin N → Bool := fun v => decide (v ≠ u0) && symGraph G u0 v
    obtain ⟨emb, hmono, hPT⟩ := embed_of_card_ge PT hT
    let Gsub : Fin M2 → Fin M2 → Bool := fun a b => G (emb a) (emb b)
    rcases h2 Gsub with ⟨f, hf, hfc⟩ | ⟨g, hg, hgc⟩
    · left
      exact ⟨fun i => emb (f i), hf.comp hmono, hfc⟩
    · right
      have hg' : IsBoolClique G true (fun i => emb (g i)) := ⟨hg.comp hmono, hgc⟩
      refine clique_extend_with_hub G true u0 _ hg' ?_ ?_
      · intro i
        have := hPT (g i)
        simp [PT] at this
        exact this.1
      · intro i
        have := hPT (g i)
        simp [PT] at this
        exact this.2

/-- **Erdős–Szekeres Step**: `R(s + 1, t + 1) ≤ R(s, t + 1) + R(s + 1, t)`. -/
theorem erdos_szekeres_step {M1 M2 s t : Nat}
    (h1 : GraphRamseyUpper M1 s (t + 1)) (h2 : GraphRamseyUpper M2 (s + 1) t)
    (hM1 : M1 ≥ 1) (hM2 : M2 ≥ 1) :
    GraphRamseyUpper (M1 + M2) (s + 1) (t + 1) := by
  intro G
  let u0 : Fin (M1 + M2) := ⟨0, by omega⟩
  have hsum := sumFin_ne_self (M1 + M2) u0
  have hge : M1 + M2 - 1 ≤ sumFin (M1 + M2) (fun v => if u0 = v then 0 else 1) := by omega
  have hlt_or : M1 ≤ sumFin (M1 + M2) (fun v => if (decide (v ≠ u0) && !(symGraph G u0 v)) then 1 else 0) ∨
      M2 ≤ sumFin (M1 + M2) (fun v => if (decide (v ≠ u0) && symGraph G u0 v) then 1 else 0) := by
    have hsplit := degree_split_pivot G u0 (M1 := M1) (M2 := M2 - 1) (by omega)
    have hadj := sumFin_add (M1 + M2)
      (fun v => if (decide (v ≠ u0) && !(symGraph G u0 v)) then 1 else 0)
      (fun v => if (decide (v ≠ u0) && symGraph G u0 v) then 1 else 0)
    have htot : sumFin (M1 + M2) (fun v => if (decide (v ≠ u0) && !(symGraph G u0 v)) then 1 else 0) +
        sumFin (M1 + M2) (fun v => if (decide (v ≠ u0) && symGraph G u0 v) then 1 else 0) = M1 + M2 - 1 := by
      have heq : (fun v : Fin (M1 + M2) =>
          (if (decide (v ≠ u0) && !(symGraph G u0 v)) then 1 else 0) +
          (if (decide (v ≠ u0) && symGraph G u0 v) then 1 else 0)) =
          (fun v : Fin (M1 + M2) => if u0 = v then 0 else 1) := by
        funext v
        by_cases hv : v = u0
        · simp [hv]
        · have hvu : ¬ (u0 = v) := fun h => hv h.symm
          cases symGraph G u0 v <;> simp [hv, hvu]
      rw [← hadj, heq]
      omega
    omega
  exact extend_from_pivot G u0 h1 h2 hlt_or

/-- Explicit Erdős–Szekeres bound `C(s + t - 2, s - 1)`. -/
def erdosSzekeresBound : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 0
  | 1, _ => 1
  | _, 1 => 1
  | s + 2, t + 2 => erdosSzekeresBound (s + 1) (t + 2) + erdosSzekeresBound (s + 2) (t + 1)

theorem erdosSzekeresBound_pos : ∀ s t : Nat, s ≥ 1 → t ≥ 1 → erdosSzekeresBound s t ≥ 1
  | 0, _, hs, _ => by omega
  | _, 0, _, ht => by omega
  | 1, t + 1, _, _ => by simp [erdosSzekeresBound]
  | s + 2, 1, _, _ => by simp [erdosSzekeresBound]
  | s + 2, t + 2, _, _ => by
    have h1 := erdosSzekeresBound_pos (s + 1) (t + 2) (by omega) (by omega)
    rw [erdosSzekeresBound]
    omega

theorem erdos_szekeres :
    ∀ s t : Nat, s ≥ 1 → t ≥ 1 → GraphRamseyUpper (erdosSzekeresBound s t) s t
  | 0, _, hs, _ => by omega
  | _, 0, _, ht => by omega
  | 1, t + 1, _, _ => by
    simpa [erdosSzekeresBound] using ramsey_left_one 1 (t + 1) (Nat.le_refl 1)
  | s + 2, 1, _, _ => by
    simpa [erdosSzekeresBound] using ramsey_right_one 1 (s + 2) (Nat.le_refl 1)
  | s + 2, t + 2, _, _ => by
    rw [erdosSzekeresBound]
    exact erdos_szekeres_step
      (erdos_szekeres (s + 1) (t + 2) (by omega) (by omega))
      (erdos_szekeres (s + 2) (t + 1) (by omega) (by omega))
      (erdosSzekeresBound_pos (s + 1) (t + 2) (by omega) (by omega))
      (erdosSzekeresBound_pos (s + 2) (t + 1) (by omega) (by omega))

/-- **Unconditional Finite Graph Ramsey Theorem**. -/
theorem graph_ramsey (s t : Nat) (hs : s ≥ 1) (ht : t ≥ 1) :
    ∃ N : Nat, N ≥ 1 ∧ GraphRamseyUpper N s t :=
  ⟨erdosSzekeresBound s t, erdosSzekeresBound_pos s t hs ht, erdos_szekeres s t hs ht⟩

/-- **Handshaking Lemma (`% 2`)**: the sum of degrees of any loopless symmetric matrix is even. -/
theorem handshaking_even :
    ∀ {N : Nat} (H : Fin N → Fin N → Nat),
      (∀ u : Fin N, H u u = 0) →
      (∀ u v : Fin N, H u v = H v u) →
      (sumFin N (fun u => sumFin N (fun v => H u v))) % 2 = 0
  | 0, _, _, _ => rfl
  | N + 1, H, hdiag, hsym => by
    let Htail : Fin N → Fin N → Nat :=
      fun u v => H ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩ ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩
    have ih := handshaking_even Htail
      (fun u => hdiag ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩)
      (fun u v => hsym _ _)
    let row0 : Nat := sumFin N (fun v => H ⟨0, Nat.zero_lt_succ N⟩ ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩)
    let col0 : Nat := sumFin N (fun u => H ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩ ⟨0, Nat.zero_lt_succ N⟩)
    have hcolEq : col0 = row0 := by
      dsimp only [col0, row0]
      have hfun : (fun u : Fin N => H ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩ ⟨0, Nat.zero_lt_succ N⟩) =
          (fun v : Fin N => H ⟨0, Nat.zero_lt_succ N⟩ ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩) :=
        funext fun u => hsym _ _
      rw [hfun]
    have hsum0 : sumFin (N + 1) (fun v => H ⟨0, Nat.zero_lt_succ N⟩ v) = row0 := by
      dsimp only [sumFin]
      rw [hdiag ⟨0, Nat.zero_lt_succ N⟩, Nat.zero_add]
    have hrest :
        sumFin N (fun u => sumFin (N + 1) (fun v => H ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩ v)) =
        col0 + sumFin N (fun u => sumFin N (fun v => Htail u v)) := by
      dsimp only [col0, Htail]
      rw [← sumFin_add]
      rfl
    change (sumFin (N + 1) (fun v => H ⟨0, Nat.zero_lt_succ N⟩ v) +
        sumFin N (fun u => sumFin (N + 1) (fun v => H ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩ v))) % 2 = 0
    rw [hsum0, hrest, hcolEq]
    omega

private theorem odd_mul_odd {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) : (a * b) % 2 = 1 := by
  rw [Nat.mul_mod, ha, hb]

/-- **Greenwood–Gleason Parity Tightening**: when both recursive bounds `M₁, M₂ ≥ 2` are even,
`R(s + 1, t + 1) ≤ M₁ + M₂ - 1` (e.g. `R(3, 4) ≤ 4 + 6 - 1 = 9`). -/
theorem erdos_szekeres_even {M1 M2 s t : Nat}
    (h1 : GraphRamseyUpper M1 s (t + 1)) (h2 : GraphRamseyUpper M2 (s + 1) t)
    (hM1 : M1 ≥ 2) (hM2 : M2 ≥ 2) (he1 : M1 % 2 = 0) (he2 : M2 % 2 = 0) :
    GraphRamseyUpper (M1 + M2 - 1) (s + 1) (t + 1) := by
  intro G
  let N := M1 + M2 - 1
  let H : Fin N → Fin N → Nat :=
    fun u v => if (decide (v ≠ u) && !(symGraph G u v)) then 1 else 0
  have hdiag : ∀ u : Fin N, H u u = 0 := fun u => by simp [H]
  have hsym : ∀ u v : Fin N, H u v = H v u := fun u v => by
    dsimp only [H]
    rw [symGraph_comm]
    by_cases h : v = u
    · simp [h]
    · have hne : u ≠ v := fun h' => h h'.symm
      simp [h, hne]
  have heven := handshaking_even H hdiag hsym
  letI : Decidable (∃ u : Fin N, M1 ≤ sumFin N (fun v => H u v)) :=
    decExistsFin N (fun u => M1 ≤ sumFin N (fun v => H u v))
  by_cases hexF : ∃ u : Fin N, M1 ≤ sumFin N (fun v => H u v)
  · obtain ⟨u0, hF⟩ := hexF
    exact extend_from_pivot G u0 h1 h2 (Or.inl hF)
  · letI : Decidable (∃ u : Fin N,
        M2 ≤ sumFin N (fun v => if (decide (v ≠ u) && symGraph G u v) then 1 else 0)) :=
      decExistsFin N (fun u =>
        M2 ≤ sumFin N (fun v => if (decide (v ≠ u) && symGraph G u v) then 1 else 0))
    by_cases hexT : ∃ u : Fin N,
        M2 ≤ sumFin N (fun v => if (decide (v ≠ u) && symGraph G u v) then 1 else 0)
    · obtain ⟨u0, hT⟩ := hexT
      exact extend_from_pivot G u0 h1 h2 (Or.inr hT)
    · exfalso
      have hreg : ∀ u : Fin N, sumFin N (fun v => H u v) = M1 - 1 := by
        intro u
        have hltF : sumFin N (fun v => H u v) ≤ M1 - 1 := by
          have := Nat.lt_of_not_le (fun hm => hexF ⟨u, hm⟩)
          omega
        have hltT : sumFin N (fun v => if (decide (v ≠ u) && symGraph G u v) then 1 else 0) ≤ M2 - 1 := by
          have := Nat.lt_of_not_le (fun hm => hexT ⟨u, hm⟩)
          omega
        have hadd := sumFin_add N
          (fun v => H u v)
          (fun v => if (decide (v ≠ u) && symGraph G u v) then 1 else 0)
        have heq : (fun v : Fin N =>
            H u v + (if (decide (v ≠ u) && symGraph G u v) then 1 else 0)) =
            (fun v : Fin N => if u = v then 0 else 1) := by
          funext v
          by_cases hv : v = u
          · simp [H, hv]
          · have hvu : ¬ (u = v) := fun h => hv h.symm
            cases hsg : symGraph G u v <;> simp [H, hv, hvu, hsg]
        have hself := sumFin_ne_self N u
        rw [heq] at hadd
        have hsum : sumFin N (fun v => H u v) +
            sumFin N (fun v => if (decide (v ≠ u) && symGraph G u v) then 1 else 0) = M1 + M2 - 2 := by
          omega
        omega
      have htot : sumFin N (fun u => sumFin N (fun v => H u v)) = N * (M1 - 1) := by
        rw [show (fun u : Fin N => sumFin N (fun v => H u v)) = (fun _ => M1 - 1) from funext hreg]
        exact sumFin_const N (M1 - 1)
      have hNodd : N % 2 = 1 := by omega
      have hModd : (M1 - 1) % 2 = 1 := by omega
      have hprod := odd_mul_odd hNodd hModd
      rw [htot, hprod] at heven
      omega

/-- Multicolor triangle Ramsey step: `R_{r+1}(3) ≤ (r + 1) * (R_r(3) - 1) + 2`. -/
theorem ramsey_triangle_step {M r : Nat} (hM : M ≥ 1) (hr : r ≥ 1)
    (h : MulticolorRamseyUpper M r 3) :
    MulticolorRamseyUpper ((r + 1) * (M - 1) + 2) (r + 1) 3 := by
  intro c
  let N := (r + 1) * (M - 1) + 2
  let u0 : Fin N := ⟨0, by dsimp [N]; omega⟩
  let symC (u v : Fin N) : Fin (r + 1) :=
    if u.val < v.val then c u v else c v u
  let degCol (col : Fin (r + 1)) : Nat :=
    sumFin N (fun v => if decide (v ≠ u0) && decide (symC u0 v = col) then 1 else 0)
  have hdeg_sum : sumFin (r + 1) degCol = N - 1 := by
    dsimp only [degCol]
    rw [sumFin_comm (r + 1) N]
    have hpt : ∀ v : Fin N,
        sumFin (r + 1) (fun col => if decide (v ≠ u0) && decide (symC u0 v = col) then 1 else 0) =
        if u0 = v then 0 else 1 := by
      intro v
      by_cases hv : v = u0
      · have : (fun col : Fin (r + 1) =>
            if decide (v ≠ u0) && decide (symC u0 v = col) then 1 else 0) = fun _ => 0 := by
          funext col
          simp [hv]
        rw [this, sumFin_const]
        simp [hv]
      · have hvu : ¬ (u0 = v) := fun h' => hv h'.symm
        have : (fun col : Fin (r + 1) =>
            if decide (v ≠ u0) && decide (symC u0 v = col) then 1 else 0) =
            (fun col => if symC u0 v = col then 1 else 0) := by
          funext col
          simp [hv]
        rw [this, sumFin_indicator_eq_one]
        simp [hvu]
    rw [show (fun v : Fin N =>
        sumFin (r + 1) (fun col => if decide (v ≠ u0) && decide (symC u0 v = col) then 1 else 0)) =
        (fun v => if u0 = v then 0 else 1) from funext hpt]
    have hself := sumFin_ne_self N u0
    omega
  letI : Decidable (∃ col : Fin (r + 1), M ≤ degCol col) :=
    decExistsFin (r + 1) (fun col => M ≤ degCol col)
  have hex : ∃ col : Fin (r + 1), M ≤ degCol col := by
    by_cases hcol : ∃ col : Fin (r + 1), M ≤ degCol col
    · exact hcol
    · exfalso
      have hle : ∀ col : Fin (r + 1), degCol col ≤ M - 1 := fun col => by
        have := Nat.lt_of_not_le (fun hm => hcol ⟨col, hm⟩)
        omega
      have hbound := sumFin_le_mul (r + 1) (M - 1) degCol hle
      rw [hdeg_sum] at hbound
      dsimp [N] at hbound
      omega
  obtain ⟨col0, hdeg0⟩ := hex
  let P : Fin N → Bool := fun v => decide (v ≠ u0) && decide (symC u0 v = col0)
  obtain ⟨emb, hmono, hP⟩ := embed_of_card_ge P hdeg0
  -- If any edge inside emb has color col0, we get a col0-triangle with u0!
  letI : Decidable (∃ a b : Fin M, a.val < b.val ∧ c (emb a) (emb b) = col0) :=
    decExistsFin M (fun a => ∃ b : Fin M, a.val < b.val ∧ c (emb a) (emb b) = col0)
  by_cases htri : ∃ a b : Fin M, a.val < b.val ∧ c (emb a) (emb b) = col0
  · obtain ⟨a, b, hab, hcab⟩ := htri
    have hne_a : emb a ≠ u0 := by have := hP a; simp [P] at this; exact this.1
    have hne_b : emb b ≠ u0 := by have := hP b; simp [P] at this; exact this.1
    have hadj_a : symC u0 (emb a) = col0 := by have := hP a; simp [P] at this; exact this.2
    have hadj_b : symC u0 (emb b) = col0 := by have := hP b; simp [P] at this; exact this.2
    -- Note u0 = 0 < emb a < emb b!
    have h0a : u0.val < (emb a).val := by
      have hlt0 : (emb a).val ≠ 0 := fun hz => hne_a (Fin.ext hz)
      dsimp [u0]; omega
    have h0b : u0.val < (emb b).val := by
      have hlt0 : (emb b).val ≠ 0 := fun hz => hne_b (Fin.ext hz)
      dsimp [u0]; omega
    have ca0 : c u0 (emb a) = col0 := by simpa [symC, h0a] using hadj_a
    have cb0 : c u0 (emb b) = col0 := by simpa [symC, h0b] using hadj_b
    refine ⟨col0, fun i => match i.val with | 0 => u0 | 1 => emb a | _ => emb b, ?_, ?_⟩
    · intro ⟨iv, hiv⟩ ⟨jv, hjv⟩ hij
      dsimp only at hij ⊢
      match iv, jv with
      | 0, 1 => exact h0a
      | 0, 2 => exact h0b
      | 1, 2 => exact hmono a b hab
      | 0, 0 | 1, 0 | 1, 1 | 2, _ | _ + 3, _ | _, _ + 3 => omega
    · intro ⟨iv, hiv⟩ ⟨jv, hjv⟩ hij
      dsimp only at hij ⊢
      match iv, jv with
      | 0, 1 => exact ca0
      | 0, 2 => exact cb0
      | 1, 2 => exact hcab
      | 0, 0 | 1, 0 | 1, 1 | 2, _ | _ + 3, _ | _, _ + 3 => omega
  · -- Map all other r colors into `Fin r` cleanly via dropCol
    let dropCol (x : Fin (r + 1)) : Fin r :=
      if hx : x.val < col0.val then ⟨x.val, by have := col0.isLt; omega⟩
      else if x.val = col0.val then ⟨0, hr⟩
      else ⟨x.val - 1, by have := x.isLt; omega⟩
    let cSub : Fin M → Fin M → Fin r := fun a b => dropCol (c (emb a) (emb b))
    obtain ⟨colSub, f, hfMono, hfC⟩ := h cSub
    let liftCol : Fin r → Fin (r + 1) := fun y =>
      if y.val < col0.val then ⟨y.val, by omega⟩ else ⟨y.val + 1, by have := y.isLt; omega⟩
    have hdrop_lift : ∀ x : Fin (r + 1), x ≠ col0 → liftCol (dropCol x) = x := by
      intro x hne
      have hnev : x.val ≠ col0.val := fun hv => hne (Fin.ext hv)
      dsimp only [dropCol, liftCol]
      by_cases hlt : x.val < col0.val
      · simp [hlt]
      · have hgt : col0.val < x.val := by omega
        have hlt2 : ¬ (x.val - 1 < col0.val) := by omega
        simp only [hlt, hnev, ↓reduceDIte, ↓reduceIte, hlt2]
        apply Fin.ext
        dsimp only
        omega
    refine ⟨liftCol colSub, fun i => emb (f i), hfMono.comp hmono, fun i j hij => ?_⟩
    have hne : c (emb (f i)) (emb (f j)) ≠ col0 := fun heq =>
      htri ⟨f i, f j, hfMono i j hij, heq⟩
    exact (hdrop_lift _ hne).symm.trans (congrArg liftCol (hfC i j hij))

private def mono1_dim (r : Nat) : Nat :=
  match r with
  | 0 => 0
  | 1 => 3
  | r' + 1 => (r' + 1) * (mono1_dim r' - 1) + 2

private theorem mono1_dim_pos : ∀ r : Nat, r ≥ 1 → mono1_dim r ≥ 1
  | 0, hr => by omega
  | 1, _ => by simp [mono1_dim]
  | r' + 2, _ => by
    have _ := mono1_dim_pos (r' + 1) (by omega)
    change (r' + 2) * (mono1_dim (r' + 1) - 1) + 2 ≥ 1
    omega

theorem multicolor_triangle_ramsey :
    ∀ r : Nat, r ≥ 1 → MulticolorRamseyUpper (mono1_dim r) r 3
  | 0, hr => by omega
  | 1, _ => by
    intro c
    exact ⟨⟨0, by decide⟩, fun i => ⟨i.val, by change i.val < 3; exact i.isLt⟩,
      fun _ _ hij => hij, fun i j _ => Fin.ext (by
        let v := c ⟨i.val, i.isLt⟩ ⟨j.val, j.isLt⟩
        have hv := v.isLt
        dsimp only
        omega)⟩
  | r' + 2, _ => by
    have ih := multicolor_triangle_ramsey (r' + 1) (by omega)
    exact ramsey_triangle_step (mono1_dim_pos (r' + 1) (by omega)) (by omega) ih

/-- **Unconditional Multicolor Triangle Ramsey Theorem**. -/
theorem ramsey_multicolor_triangles (r : Nat) (hr : r ≥ 1) :
    ∃ N : Nat, N ≥ 1 ∧ MulticolorRamseyUpper N r 3 :=
  ⟨mono1_dim r, mono1_dim_pos r hr, multicolor_triangle_ramsey r hr⟩

/-- Fast branch-and-prune clique absence verification. -/
def allPairOk {N : Nat} (G : Fin N → Fin N → Bool) (col : Bool) (v : Nat) : List Nat → Bool
  | [] => true
  | u :: rest =>
    (if hu : u < N then
      if hv : v < N then
        (G ⟨u, hu⟩ ⟨v, hv⟩ == col)
      else false
    else false) && allPairOk G col v rest

def hasCliqueLoop (N : Nat) (G : Fin N → Fin N → Bool) (col : Bool)
    (nextV : Nat) (chosen : List Nat) (rem : Nat)
    (step : Nat → List Nat → Bool) : Bool :=
  match rem with
  | 0 => false
  | rem' + 1 =>
    (allPairOk G col nextV chosen && step (nextV + 1) (nextV :: chosen)) ||
    hasCliqueLoop N G col (nextV + 1) chosen rem' step

def hasCliqueAux (N : Nat) (G : Fin N → Fin N → Bool) (col : Bool) :
    Nat → Nat → List Nat → Bool
  | 0, _, _ => true
  | need + 1, nextV, chosen =>
    hasCliqueLoop N G col nextV chosen (N - nextV) (hasCliqueAux N G col need)

def checkNoClique (N : Nat) (G : Fin N → Fin N → Bool) (col : Bool) (k : Nat) : Bool :=
  !hasCliqueAux N G col k 0 []

private theorem hasCliqueLoop_hit (N : Nat) (G : Fin N → Fin N → Bool) (col : Bool)
    (step : Nat → List Nat → Bool) (chosen : List Nat) (v : Nat) :
    ∀ (kstep rem nextV : Nat),
      v = nextV + kstep →
      kstep < rem →
      allPairOk G col v chosen = true →
      step (v + 1) (v :: chosen) = true →
      hasCliqueLoop N G col nextV chosen rem step = true
  | _, 0, _, _, hlt, _, _ => absurd hlt (Nat.not_lt_zero _)
  | 0, _ + 1, nextV, heq, _, hpair, hstep => by
    have hveq : nextV = v := by omega
    subst hveq
    simp [hasCliqueLoop, hpair, hstep]
  | kstep' + 1, rem' + 1, nextV, heq, hlt, hpair, hstep => by
    have ih := hasCliqueLoop_hit N G col step chosen v kstep' rem' (nextV + 1)
      (by omega) (Nat.lt_of_succ_lt_succ hlt) hpair hstep
    simp [hasCliqueLoop, ih]

private theorem hasClique_of_isBoolClique {N k : Nat} (G : Fin N → Fin N → Bool) (col : Bool)
    (f : Fin k → Fin N) (hf : IsBoolClique G col f) :
    ∀ (m j nextV : Nat) (hj : j + m = k) (chosen : List Nat),
      (∀ p ∈ chosen, ∃ (a : Fin k), a.val < j ∧ (f a).val = p ∧ (∀ hlt : a.val < k, f ⟨a.val, hlt⟩ = f a)) →
      (∀ hm : 0 < m, nextV ≤ (f ⟨j, by omega⟩).val) →
      hasCliqueAux N G col m nextV chosen = true
  | 0, _, _, _, _, _, _ => rfl
  | m' + 1, j, nextV, hj, chosen, hch, hle => by
    let fj : Fin k := ⟨j, by omega⟩
    let v := (f fj).val
    have hv_lt : v < N := (f fj).isLt
    have hv_ge : nextV ≤ v := hle (Nat.zero_lt_succ m')
    have hpair : allPairOk G col v chosen = true := by
      clear hle
      induction chosen with
      | nil => rfl
      | cons u rest ih_u =>
        obtain ⟨a, ha_lt, ha_eq, _⟩ := hch u List.mem_cons_self
        have ha_fin : a.val < fj.val := ha_lt
        have hlt_u : (f a).val < v := hf.1 a fj ha_fin
        have hua : u < N := ha_eq ▸ (f a).isLt
        have hG : G ⟨u, hua⟩ ⟨v, hv_lt⟩ = col := by
          have := hf.2 a fj ha_fin
          have hf1 : f a = ⟨u, hua⟩ := Fin.ext ha_eq
          have hf2 : f fj = ⟨v, hv_lt⟩ := rfl
          simpa [hf1, hf2] using this
        have hrest : allPairOk G col v rest = true :=
          ih_u (fun p hp => hch p (List.mem_cons_of_mem _ hp))
        simp [allPairOk, hua, hv_lt, hG, hrest]
    have hnext : hasCliqueAux N G col m' (v + 1) (v :: chosen) = true := by
      refine hasClique_of_isBoolClique G col f hf m' (j + 1) (v + 1) (by omega) (v :: chosen) ?_ ?_
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hmem
        · exact ⟨fj, Nat.lt_succ_self j, rfl, fun _ => rfl⟩
        · obtain ⟨a, ha_lt, ha_eq, _⟩ := hch p hmem
          exact ⟨a, Nat.lt_succ_of_lt ha_lt, ha_eq, fun _ => rfl⟩
      · intro hm'
        have hlt_j : fj.val < j + 1 := Nat.lt_succ_self j
        have := hf.1 fj ⟨j + 1, by omega⟩ hlt_j
        exact this
    dsimp only [hasCliqueAux]
    exact hasCliqueLoop_hit N G col (hasCliqueAux N G col m') chosen v
      (v - nextV) (N - nextV) nextV (by omega) (by omega) hpair hnext

/-- Certifies `¬ ∃ f, IsBoolClique G col f` whenever `checkNoClique N G col k = true`. -/
theorem noBoolClique_of_check {N k : Nat} {G : Fin N → Fin N → Bool} {col : Bool}
    (h : checkNoClique N G col k = true) : ¬ ∃ f : Fin k → Fin N, IsBoolClique G col f := by
  rintro ⟨f, hf⟩
  have htrue := hasClique_of_isBoolClique G col f hf k 0 0 (Nat.zero_add k) []
    (fun _ hm => nomatch hm) (fun _ => Nat.zero_le _)
  simp [checkNoClique, htrue] at h

/-- Lower-bound verifier for 2-color graph Ramsey: `checkNoClique N G false s = true` and
`checkNoClique N G true t = true` certifies `¬ GraphRamseyUpper N s t`. -/
theorem checkNoClique_sound {N s t : Nat} (G : Fin N → Fin N → Bool)
    (hs : checkNoClique N G false s = true) (ht : checkNoClique N G true t = true) :
    ¬ GraphRamseyUpper N s t := by
  intro hR
  rcases hR G with hf | ht'
  · exact noBoolClique_of_check hs hf
  · exact noBoolClique_of_check ht ht'

/-- Lower-bound verifier for multicolor Ramsey: if every color `col : Fin r` passes `checkNoClique`,
then `¬ MulticolorRamseyUpper N r k`. -/
theorem checkNoMonoClique_sound {N r k : Nat} (c : Fin N → Fin N → Fin r)
    (h : ∀ col : Fin r, checkNoClique N (fun u v => decide (c u v = col)) true k = true) :
    ¬ MulticolorRamseyUpper N r k := by
  intro hR
  obtain ⟨col, f, hfMono, hfC⟩ := hR c
  have hbool : IsBoolClique (fun u v => decide (c u v = col)) true f :=
    ⟨hfMono, fun i j hij => decide_eq_true (hfC i j hij)⟩
  exact noBoolClique_of_check (h col) ⟨f, hbool⟩

end HJBrigade
