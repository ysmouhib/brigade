import HJBrigade.Density.Sperner

/-!
# 9-Bit `[3]^2` Slice Encoding and Gluing Helpers

Provides fast, kernel-verified packing between `Word 2 3 → Bool` and `Fin 512`,
plus `glue3` to assemble `Word 3 3 → Bool` subsets from three `[3]^2` slices.
Used by both `ExactDHJ` (`c_{4,3} = 52`) and `Moser` (`c'_{3,3} = 16`).
-/

namespace HJBrigade

def idxOfW2 (w : Word 2 3) : Fin 9 :=
  ⟨(w ⟨0, Nat.zero_lt_succ 1⟩).val + 3 * (w ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩).val, by
    have h0 := (w ⟨0, Nat.zero_lt_succ 1⟩).isLt
    have h1 := (w ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩).isLt
    omega⟩

def w2OfIdx (k : Fin 9) : Word 2 3 :=
  fun i => if i.val = 0 then ⟨k.val % 3, by omega⟩ else ⟨k.val / 3, by have := k.isLt; omega⟩

theorem w2OfIdx_idxOfW2 (w : Word 2 3) : w2OfIdx (idxOfW2 w) = w := by
  funext ⟨i, hi⟩
  have h0 := (w ⟨0, Nat.zero_lt_succ 1⟩).isLt
  have h1 := (w ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩).isLt
  match i with
  | 0 =>
    apply Fin.ext
    dsimp [w2OfIdx, idxOfW2]
    omega
  | 1 =>
    apply Fin.ext
    dsimp [w2OfIdx, idxOfW2]
    omega
  | _ + 2 => omega

theorem idxOfW2_w2OfIdx (k : Fin 9) : idxOfW2 (w2OfIdx k) = k := by
  revert k
  decide

private def bitVal (b : Bool) : Nat := if b then 1 else 0

private theorem bitVal_le (b : Bool) : bitVal b ≤ 1 := by
  cases b <;> decide

private theorem mod2_add_mul2 (b : Bool) (n : Nat) :
    ((bitVal b + 2 * n) % 2 == 1) = b := by
  cases b <;> simp [bitVal] <;> omega

private theorem div2_add_mul2 (b : Bool) (n : Nat) :
    (bitVal b + 2 * n) / 2 = n := by
  cases b <;> simp [bitVal] <;> omega

private theorem mod2_bitVal (b : Bool) : (bitVal b % 2 == 1) = b := by
  cases b <;> rfl

def pack9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 512 :=
  ⟨bitVal b0 + 2 * (bitVal b1 + 2 * (bitVal b2 + 2 * (bitVal b3 + 2 * (bitVal b4 +
    2 * (bitVal b5 + 2 * (bitVal b6 + 2 * (bitVal b7 + 2 * bitVal b8))))))), by
    have h0 := bitVal_le b0; have h1 := bitVal_le b1; have h2 := bitVal_le b2
    have h3 := bitVal_le b3; have h4 := bitVal_le b4; have h5 := bitVal_le b5
    have h6 := bitVal_le b6; have h7 := bitVal_le b7; have h8 := bitVal_le b8
    omega⟩

def testBit9 : Nat → Nat → Bool
  | m, 0 => (m % 2) == 1
  | m, j + 1 => testBit9 (m / 2) j

def decode2 (m : Fin 512) (w : Word 2 3) : Bool :=
  testBit9 m.val (idxOfW2 w).val

def encode2 (B : Word 2 3 → Bool) : Fin 512 :=
  pack9
    (B (w2OfIdx ⟨0, by decide⟩))
    (B (w2OfIdx ⟨1, by decide⟩))
    (B (w2OfIdx ⟨2, by decide⟩))
    (B (w2OfIdx ⟨3, by decide⟩))
    (B (w2OfIdx ⟨4, by decide⟩))
    (B (w2OfIdx ⟨5, by decide⟩))
    (B (w2OfIdx ⟨6, by decide⟩))
    (B (w2OfIdx ⟨7, by decide⟩))
    (B (w2OfIdx ⟨8, by decide⟩))

private theorem testBit_pack9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) (j : Fin 9) :
    testBit9 (pack9 b0 b1 b2 b3 b4 b5 b6 b7 b8).val j.val =
      match j.val with
      | 0 => b0
      | 1 => b1
      | 2 => b2
      | 3 => b3
      | 4 => b4
      | 5 => b5
      | 6 => b6
      | 7 => b7
      | _ => b8 := by
  rcases j with ⟨jv, hjv⟩
  dsimp only [pack9]
  match jv with
  | 0 => exact mod2_add_mul2 b0 _
  | 1 => dsimp only [testBit9]; rw [div2_add_mul2]; exact mod2_add_mul2 b1 _
  | 2 => dsimp only [testBit9]; rw [div2_add_mul2, div2_add_mul2]; exact mod2_add_mul2 b2 _
  | 3 => dsimp only [testBit9]; rw [div2_add_mul2, div2_add_mul2, div2_add_mul2]; exact mod2_add_mul2 b3 _
  | 4 => dsimp only [testBit9]; rw [div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2]; exact mod2_add_mul2 b4 _
  | 5 => dsimp only [testBit9]; rw [div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2]; exact mod2_add_mul2 b5 _
  | 6 => dsimp only [testBit9]; rw [div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2]; exact mod2_add_mul2 b6 _
  | 7 => dsimp only [testBit9]; rw [div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2]; exact mod2_add_mul2 b7 _
  | 8 => dsimp only [testBit9]; rw [div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2, div2_add_mul2]; exact mod2_bitVal b8
  | _ + 9 => omega

theorem decode2_encode2 (B : Word 2 3 → Bool) : decode2 (encode2 B) = B := by
  funext w
  dsimp only [decode2, encode2]
  rw [testBit_pack9]
  have hw : B w = B (w2OfIdx (idxOfW2 w)) := congrArg B (w2OfIdx_idxOfW2 w).symm
  rw [hw]
  generalize idxOfW2 w = k
  rcases k with ⟨kv, hkv⟩
  match kv with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => omega

def split512 (a b c : Fin 8) : Fin 512 :=
  ⟨a.val + 8 * b.val + 64 * c.val, by have := a.isLt; have := b.isLt; have := c.isLt; omega⟩

theorem forall_fin512 {P : Fin 512 → Prop}
    (h : ∀ a b c : Fin 8, P (split512 a b c)) : ∀ m : Fin 512, P m := by
  intro ⟨m, hm⟩
  have heq : split512 ⟨m % 8, by omega⟩ ⟨(m / 8) % 8, by omega⟩ ⟨m / 64, by omega⟩ = ⟨m, hm⟩ := by
    apply Fin.ext
    dsimp [split512]
    omega
  rw [← heq]
  exact h _ _ _

def card2 (m : Fin 512) : Nat :=
  (List.range 9).foldl (fun acc j => acc + (m.val / 2 ^ j) % 2) 0

theorem card2_eq_wordCard : ∀ m : Fin 512, card2 m = wordCard (decode2 m) :=
  forall_fin512 fun a b c => by
    revert a b c
    decide

theorem wordCard_eq_card2_encode2 (B : Word 2 3 → Bool) : wordCard B = card2 (encode2 B) := by
  have hcard := card2_eq_wordCard (encode2 B)
  rw [decode2_encode2] at hcard
  exact hcard.symm

def tailWord3 {d k : Nat} (w : Word (d + 1) k) : Word d k :=
  fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

def glue3 (m0 m1 m2 : Fin 512) (w : Word 3 3) : Bool :=
  if (w ⟨0, Nat.zero_lt_succ 2⟩).val = 0 then decode2 m0 (tailWord3 w)
  else if (w ⟨0, Nat.zero_lt_succ 2⟩).val = 1 then decode2 m1 (tailWord3 w)
  else decode2 m2 (tailWord3 w)

theorem eq_glue3 (B : Word 3 3 → Bool) :
    B = glue3
      (encode2 (fun w => B (consFin ⟨0, by decide⟩ w)))
      (encode2 (fun w => B (consFin ⟨1, by decide⟩ w)))
      (encode2 (fun w => B (consFin ⟨2, by decide⟩ w))) := by
  funext w
  dsimp only [glue3]
  have hlt := (w ⟨0, Nat.zero_lt_succ 2⟩).isLt
  match hv : (w ⟨0, Nat.zero_lt_succ 2⟩).val with
  | 0 =>
    simp only [↓reduceIte, decode2_encode2]
    congr 1
    funext ⟨i, hi⟩
    cases i with
    | zero => exact Fin.ext hv
    | succ i' => rfl
  | 1 =>
    simp only [Nat.one_ne_zero, ↓reduceIte, decode2_encode2]
    congr 1
    funext ⟨i, hi⟩
    cases i with
    | zero => exact Fin.ext hv
    | succ i' => rfl
  | 2 =>
    simp [decode2_encode2]
    congr 1
    funext ⟨i, hi⟩
    cases i with
    | zero => exact Fin.ext hv
    | succ i' => rfl
  | _ + 3 => omega

theorem wordCard_succ3 {d : Nat} (A : Word (d + 1) 3 → Bool) :
    wordCard A =
      wordCard (fun w => A (consFin ⟨0, by decide⟩ w)) +
      wordCard (fun w => A (consFin ⟨1, by decide⟩ w)) +
      wordCard (fun w => A (consFin ⟨2, by decide⟩ w)) := by
  change sumFin 3 (fun a => wordCard (fun w => A (consFin a w))) = _
  dsimp [sumFin]
  omega

end HJBrigade
