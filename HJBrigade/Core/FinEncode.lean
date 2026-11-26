import HJBrigade.Core.FinQuant

/-!
# Constructive Finite Equivalences and Function-Space Encodings

Provides `FinEquiv α n` (explicit bijection `α ≃ Fin n`) together with
`finEquivFun : FinEquiv α n → FinEquiv (Fin d → α) (n ^ d)` and injective
map encoding `encodeMap : FinEquiv α M → (α → Fin r) → Fin (r ^ M)` for
Shelah's inductive Hales–Jewett cube proof.
-/

namespace HJBrigade

/-- Explicit constructive bijection between `α` and `Fin n`. -/
structure FinEquiv (α : Type u) (n : Nat) where
  toFin : α → Fin n
  ofFin : Fin n → α
  left_inv : ∀ a, ofFin (toFin a) = a
  right_inv : ∀ i, toFin (ofFin i) = i

theorem FinEquiv.toFin_inj {α : Type u} {n : Nat} (e : FinEquiv α n) {x y : α}
    (h : e.toFin x = e.toFin y) : x = y := by
  calc
    x = e.ofFin (e.toFin x) := (e.left_inv x).symm
    _ = e.ofFin (e.toFin y) := congrArg e.ofFin h
    _ = y := e.left_inv y

def finEquivFin (n : Nat) : FinEquiv (Fin n) n where
  toFin := id
  ofFin := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private theorem div_lt_of_lt_mul_left {x a b : Nat} (h : x < a * b) : x / a < b :=
  Classical.byContradiction fun hge => by
    have hle : b ≤ x / a := Nat.le_of_not_lt hge
    have h1 : a * b ≤ a * (x / a) := Nat.mul_le_mul_left a hle
    have h2 : a * (x / a) ≤ x := Nat.mul_div_le x a
    omega

private theorem pair_lt_pow {a b n d : Nat} (ha : a < n) (hb : b < n ^ d) :
    a + n * b < n ^ (d + 1) := by
  have hb1 : b + 1 ≤ n ^ d := hb
  have hmul : n * (b + 1) ≤ n * n ^ d := Nat.mul_le_mul_left n hb1
  have hpow : n * n ^ d = n ^ (d + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [Nat.mul_add, Nat.mul_one, hpow] at hmul
  omega

private theorem consFin_zero {d : Nat} {α : Type u} (a : α) (g : Fin d → α) :
    consFin a g ⟨0, Nat.zero_lt_succ d⟩ = a := rfl

private theorem consFin_tail {d : Nat} {α : Type u} (a : α) (g : Fin d → α) :
    (fun i : Fin d => consFin a g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) = g := rfl

/-- Constructive bijection `(Fin d → α) ≃ Fin (n ^ d)` from `α ≃ Fin n`. -/
def finEquivFun {α : Type u} {n : Nat} (e : FinEquiv α n) :
    ∀ (d : Nat), FinEquiv (Fin d → α) (n ^ d)
  | 0 =>
    { toFin := fun _ => ⟨0, by simp⟩
      ofFin := fun _ => Fin.elim0
      left_inv := fun f => elim0_eta f
      right_inv := fun ⟨v, hv⟩ => Fin.ext (by simp only [Nat.pow_zero] at hv; dsimp; omega) }
  | d + 1 =>
    if hn : n = 0 then
      { toFin := fun f => by
          have h0 : Fin 0 := ⟨(e.toFin (f ⟨0, Nat.zero_lt_succ d⟩)).val,
            by simpa [hn] using (e.toFin (f ⟨0, Nat.zero_lt_succ d⟩)).isLt⟩
          exact h0.elim0
        ofFin := fun i => by
          have h0 : Fin 0 := ⟨i.val, by simpa [hn] using i.isLt⟩
          exact h0.elim0
        left_inv := fun f => by
          have h0 : Fin 0 := ⟨(e.toFin (f ⟨0, Nat.zero_lt_succ d⟩)).val,
            by simpa [hn] using (e.toFin (f ⟨0, Nat.zero_lt_succ d⟩)).isLt⟩
          exact h0.elim0
        right_inv := fun i => by
          have h0 : Fin 0 := ⟨i.val, by simpa [hn] using i.isLt⟩
          exact h0.elim0 }
    else
      let hn_pos : n ≥ 1 := Nat.pos_of_ne_zero hn
      let ih := finEquivFun e d
      { toFin := fun f =>
          let a := e.toFin (f ⟨0, Nat.zero_lt_succ d⟩)
          let b := ih.toFin (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          ⟨a.val + n * b.val, pair_lt_pow a.isLt b.isLt⟩
        ofFin := fun idx =>
          have hpow : n ^ (d + 1) = n * n ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
          have hdiv : idx.val / n < n ^ d :=
            div_lt_of_lt_mul_left (Nat.lt_of_lt_of_eq idx.isLt hpow)
          consFin (e.ofFin ⟨idx.val % n, Nat.mod_lt idx.val hn_pos⟩)
            (ih.ofFin ⟨idx.val / n, hdiv⟩)
        left_inv := fun f => by
          dsimp
          let a := e.toFin (f ⟨0, Nat.zero_lt_succ d⟩)
          let b := ih.toFin (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          have hmod : (a.val + n * b.val) % n = a.val := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
          have hdiv : (a.val + n * b.val) / n = b.val := by
            rw [Nat.add_mul_div_left a.val b.val hn_pos, Nat.div_eq_of_lt a.isLt, Nat.zero_add]
          have haFin : (⟨(a.val + n * b.val) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = a :=
            Fin.ext hmod
          have hpow : n ^ (d + 1) = n * n ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
          have hdivLt : (a.val + n * b.val) / n < n ^ d :=
            div_lt_of_lt_mul_left (Nat.lt_of_lt_of_eq (pair_lt_pow a.isLt b.isLt) hpow)
          have hbFin : (⟨(a.val + n * b.val) / n, hdivLt⟩ : Fin (n ^ d)) = b :=
            Fin.ext hdiv
          change consFin (e.ofFin ⟨(a.val + n * b.val) % n, _⟩)
              (ih.ofFin ⟨(a.val + n * b.val) / n, hdivLt⟩) = f
          rw [haFin, hbFin, e.left_inv, ih.left_inv, consFin_eta]
        right_inv := fun idx => by
          dsimp
          apply Fin.ext
          change (e.toFin (consFin _ _ ⟨0, Nat.zero_lt_succ d⟩)).val +
              n * (ih.toFin (fun i => consFin _ _ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).val = idx.val
          rw [consFin_zero, consFin_tail, e.right_inv, ih.right_inv]
          dsimp
          have hdm := Nat.div_add_mod idx.val n
          omega }

/-- Encode any function `α → Fin r` into `Fin (r ^ M)` using `e : FinEquiv α M`. -/
def encodeMap {α : Type u} {M r : Nat} (e : FinEquiv α M) (g : α → Fin r) : Fin (r ^ M) :=
  (finEquivFun (finEquivFin r) M).toFin (fun i => g (e.ofFin i))

theorem encodeMap_inj {α : Type u} {M r : Nat} (e : FinEquiv α M)
    {g₁ g₂ : α → Fin r} (h : encodeMap e g₁ = encodeMap e g₂) :
    ∀ a : α, g₁ a = g₂ a := by
  have hfun := (finEquivFun (finEquivFin r) M).toFin_inj h
  intro a
  have hpt := congrFun hfun (e.toFin a)
  simpa [e.left_inv] using hpt

end HJBrigade
