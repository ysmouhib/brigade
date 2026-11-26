/-!
# Finite Quantification, Decidability, and Finite Pigeonhole

Constructive decidable quantification over `Fin n`, `Option α`, `Fin d → α`,
and `(Fin d → Fin k) → β` for kernel-checked `decide` proofs (no `native_decide`),
plus the finite pigeonhole principle (`fin_pigeonhole`).
-/

namespace HJBrigade

def decForallFin : ∀ (n : Nat) (P : Fin n → Prop) [∀ i, Decidable (P i)], Decidable (∀ i : Fin n, P i)
  | 0, _, _ => isTrue (fun i => i.elim0)
  | n + 1, P, _ =>
    if h0 : P ⟨0, Nat.zero_lt_succ n⟩ then
      letI : Decidable (∀ i : Fin n, P ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) :=
        decForallFin n (fun i => P ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      if hRest : ∀ i : Fin n, P ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ then
        isTrue (by
          intro ⟨v, hv⟩
          cases v with
          | zero => exact h0
          | succ v' => exact hRest ⟨v', Nat.lt_of_succ_lt_succ hv⟩)
      else
        isFalse (fun h => hRest (fun i => h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))
    else
      isFalse (fun h => h0 (h ⟨0, Nat.zero_lt_succ n⟩))

def decExistsFin : ∀ (n : Nat) (P : Fin n → Prop) [∀ i, Decidable (P i)], Decidable (∃ i : Fin n, P i)
  | 0, _, _ => isFalse (fun ⟨i, _⟩ => i.elim0)
  | n + 1, P, _ =>
    if h0 : P ⟨0, Nat.zero_lt_succ n⟩ then
      isTrue ⟨⟨0, Nat.zero_lt_succ n⟩, h0⟩
    else
      letI : Decidable (∃ i : Fin n, P ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) :=
        decExistsFin n (fun i => P ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      if hRest : ∃ i : Fin n, P ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ then
        isTrue (by
          obtain ⟨i, hi⟩ := hRest
          exact ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, hi⟩)
      else
        isFalse (by
          rintro ⟨⟨v, hv⟩, hPv⟩
          cases v with
          | zero => exact h0 hPv
          | succ v' => exact hRest ⟨⟨v', Nat.lt_of_succ_lt_succ hv⟩, hPv⟩)

class FinDomain (α : Type u) where
  decForall : ∀ (P : α → Prop) [∀ a, Decidable (P a)], Decidable (∀ a : α, P a)
  decExists : ∀ (P : α → Prop) [∀ a, Decidable (P a)], Decidable (∃ a : α, P a)

instance (priority := low) {α : Type u} [FinDomain α] (P : α → Prop) [∀ a, Decidable (P a)] :
    Decidable (∀ a : α, P a) :=
  FinDomain.decForall P

instance (priority := low) {α : Type u} [FinDomain α] (P : α → Prop) [∀ a, Decidable (P a)] :
    Decidable (∃ a : α, P a) :=
  FinDomain.decExists P

instance (n : Nat) : FinDomain (Fin n) where
  decForall := fun P _ => decForallFin n P
  decExists := fun P _ => decExistsFin n P

instance {α : Type u} [FinDomain α] : FinDomain (Option α) where
  decForall := fun P _ =>
    if h0 : P none then
      letI : Decidable (∀ a : α, P (some a)) := FinDomain.decForall (fun a : α => P (some a))
      if h1 : ∀ a : α, P (some a) then
        isTrue (fun o => match o with | none => h0 | some a => h1 a)
      else
        isFalse (fun h => h1 (fun a => h (some a)))
    else
      isFalse (fun h => h0 (h none))
  decExists := fun P _ =>
    if h0 : P none then
      isTrue ⟨none, h0⟩
    else
      letI : Decidable (∃ a : α, P (some a)) := FinDomain.decExists (fun a : α => P (some a))
      if h1 : ∃ a : α, P (some a) then
        isTrue (by obtain ⟨a, ha⟩ := h1; exact ⟨some a, ha⟩)
      else
        isFalse (by
          rintro ⟨o, ho⟩
          cases o with
          | none => exact h0 ho
          | some a => exact h1 ⟨a, ho⟩)

def consFin {d : Nat} {α : Type u} (a : α) (f : Fin d → α) : Fin (d + 1) → α
  | ⟨0, _⟩ => a
  | ⟨v + 1, hv⟩ => f ⟨v, Nat.lt_of_succ_lt_succ hv⟩

theorem consFin_eta {d : Nat} {α : Type u} (f : Fin (d + 1) → α) :
    consFin (f ⟨0, Nat.zero_lt_succ d⟩) (fun i : Fin d => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) = f := by
  funext ⟨v, hv⟩
  cases v <;> rfl

theorem elim0_eta {α : Type u} (f : Fin 0 → α) : Fin.elim0 = f := by
  funext i
  exact i.elim0

private def decForallFinFun {α : Type u} [FinDomain α] :
    ∀ (d : Nat) (P : (Fin d → α) → Prop) [∀ f, Decidable (P f)], Decidable (∀ f : Fin d → α, P f)
  | 0, P, _ =>
    if h0 : P Fin.elim0 then
      isTrue (fun f => by rw [← elim0_eta f]; exact h0)
    else
      isFalse (fun h => h0 (h Fin.elim0))
  | d + 1, P, _ =>
    letI : ∀ a : α, Decidable (∀ g : Fin d → α, P (consFin a g)) :=
      fun a => decForallFinFun d (fun g => P (consFin a g))
    letI : Decidable (∀ a : α, ∀ g : Fin d → α, P (consFin a g)) :=
      FinDomain.decForall (fun a : α => ∀ g : Fin d → α, P (consFin a g))
    if h : ∀ (a : α) (g : Fin d → α), P (consFin a g) then
      isTrue (fun f => by rw [← consFin_eta f]; exact h _ _)
    else
      isFalse (fun hall => h (fun a g => hall (consFin a g)))

private def decExistsFinFun {α : Type u} [FinDomain α] :
    ∀ (d : Nat) (P : (Fin d → α) → Prop) [∀ f, Decidable (P f)], Decidable (∃ f : Fin d → α, P f)
  | 0, P, _ =>
    if h0 : P Fin.elim0 then
      isTrue ⟨Fin.elim0, h0⟩
    else
      isFalse (fun ⟨f, hf⟩ => h0 (by rw [elim0_eta f]; exact hf))
  | d + 1, P, _ =>
    letI : ∀ a : α, Decidable (∃ g : Fin d → α, P (consFin a g)) :=
      fun a => decExistsFinFun d (fun g => P (consFin a g))
    letI : Decidable (∃ a : α, ∃ g : Fin d → α, P (consFin a g)) :=
      FinDomain.decExists (fun a : α => ∃ g : Fin d → α, P (consFin a g))
    if h : ∃ (a : α) (g : Fin d → α), P (consFin a g) then
      isTrue (by obtain ⟨a, g, hag⟩ := h; exact ⟨consFin a g, hag⟩)
    else
      isFalse (by
        rintro ⟨f, hf⟩
        rw [← consFin_eta f] at hf
        exact h ⟨f ⟨0, Nat.zero_lt_succ d⟩, fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, hf⟩)

instance {d : Nat} {α : Type u} [FinDomain α] : FinDomain (Fin d → α) where
  decForall := fun P _ => decForallFinFun d P
  decExists := fun P _ => decExistsFinFun d P

private def curryFinArrow {d k : Nat} {β : Type u}
    (c : (Fin (d + 1) → Fin k) → β) : Fin k → ((Fin d → Fin k) → β) :=
  fun a g => c (consFin a g)

private def uncurryFinArrow {d k : Nat} {β : Type u}
    (h : Fin k → ((Fin d → Fin k) → β)) : (Fin (d + 1) → Fin k) → β :=
  fun w => h (w ⟨0, Nat.zero_lt_succ d⟩) (fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private theorem uncurry_curryFinArrow {d k : Nat} {β : Type u}
    (c : (Fin (d + 1) → Fin k) → β) : uncurryFinArrow (curryFinArrow c) = c := by
  funext w
  exact congrArg c (consFin_eta w)

private def decForallFinMap {β : Type u} [FinDomain β] :
    ∀ (d k : Nat) (P : ((Fin d → Fin k) → β) → Prop) [∀ c, Decidable (P c)],
      Decidable (∀ c : (Fin d → Fin k) → β, P c)
  | 0, k, P, _ =>
    letI : Decidable (∀ b : β, P (fun _ => b)) :=
      FinDomain.decForall (fun b : β => P (fun _ => b))
    if h : ∀ b : β, P (fun _ => b) then
      isTrue (fun c => by
        have hconst : (fun _ : Fin 0 → Fin k => c Fin.elim0) = c := by
          funext w
          rw [← elim0_eta w]
        rw [← hconst]
        exact h (c Fin.elim0))
    else
      isFalse (fun hall => h (fun b => hall (fun _ => b)))
  | d + 1, k, P, _ =>
    letI : ∀ h : Fin k → ((Fin d → Fin k) → β), Decidable (P (uncurryFinArrow h)) :=
      fun h => inferInstanceAs (Decidable (P (uncurryFinArrow h)))
    letI : FinDomain ((Fin d → Fin k) → β) :=
      { decForall := fun Q _ => decForallFinMap d k Q
        decExists := fun Q _ =>
          letI : Decidable (∀ c, ¬ Q c) := decForallFinMap d k (fun c => ¬ Q c)
          if hnot : ∀ c, ¬ Q c then isFalse (fun ⟨c, hc⟩ => hnot c hc)
          else isTrue (Classical.byContradiction (fun hnex => hnot (fun c hc => hnex ⟨c, hc⟩))) }
    letI : Decidable (∀ h : Fin k → ((Fin d → Fin k) → β), P (uncurryFinArrow h)) :=
      FinDomain.decForall (fun h => P (uncurryFinArrow h))
    if h : ∀ h : Fin k → ((Fin d → Fin k) → β), P (uncurryFinArrow h) then
      isTrue (fun c => by rw [← uncurry_curryFinArrow c]; exact h (curryFinArrow c))
    else
      isFalse (fun hall => h (fun f => hall (uncurryFinArrow f)))

private def decExistsFinMapConstructive {β : Type u} [FinDomain β] :
    ∀ (d k : Nat) (P : ((Fin d → Fin k) → β) → Prop) [∀ c, Decidable (P c)],
      Decidable (∃ c : (Fin d → Fin k) → β, P c)
  | 0, k, P, _ =>
    letI : Decidable (∃ b : β, P (fun _ => b)) :=
      FinDomain.decExists (fun b : β => P (fun _ => b))
    if h : ∃ b : β, P (fun _ => b) then
      isTrue (by obtain ⟨b, hb⟩ := h; exact ⟨fun _ => b, hb⟩)
    else
      isFalse (by
        rintro ⟨c, hc⟩
        have hconst : (fun _ : Fin 0 → Fin k => c Fin.elim0) = c := by
          funext w
          rw [← elim0_eta w]
        rw [← hconst] at hc
        exact h ⟨c Fin.elim0, hc⟩)
  | d + 1, k, P, _ =>
    letI : FinDomain ((Fin d → Fin k) → β) :=
      { decForall := fun Q _ => decForallFinMap d k Q
        decExists := fun Q _ => decExistsFinMapConstructive d k Q }
    letI : Decidable (∃ h : Fin k → ((Fin d → Fin k) → β), P (uncurryFinArrow h)) :=
      FinDomain.decExists (fun h => P (uncurryFinArrow h))
    if h : ∃ h : Fin k → ((Fin d → Fin k) → β), P (uncurryFinArrow h) then
      isTrue (by obtain ⟨f, hf⟩ := h; exact ⟨uncurryFinArrow f, hf⟩)
    else
      isFalse (by
        rintro ⟨c, hc⟩
        rw [← uncurry_curryFinArrow c] at hc
        exact h ⟨curryFinArrow c, hc⟩)

instance {d k : Nat} {β : Type u} [FinDomain β] : FinDomain ((Fin d → Fin k) → β) where
  decForall := fun P _ => decForallFinMap d k P
  decExists := fun P _ => decExistsFinMapConstructive d k P

instance (priority := low) {d : Nat} {α : Type u} [DecidableEq α] : DecidableEq (Fin d → α) :=
  fun f g =>
    letI : Decidable (∀ i : Fin d, f i = g i) := decForallFin d (fun i => f i = g i)
    if h : ∀ i : Fin d, f i = g i then
      isTrue (funext h)
    else
      isFalse (fun hfg => h (fun i => congrFun hfg i))

private def skipFin {n : Nat} (k x : Fin (n + 1)) (h : x ≠ k) : Fin n :=
  if hx : x.val < k.val then
    ⟨x.val, Nat.lt_of_lt_of_le hx (Nat.le_of_lt_succ k.isLt)⟩
  else
    ⟨x.val - 1, by
      have hne : x.val ≠ k.val := fun hv => h (Fin.ext hv)
      have hgt : k.val < x.val := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hx) (Ne.symm hne)
      omega⟩

private theorem skipFin_inj {n : Nat} {k x y : Fin (n + 1)}
    (hx : x ≠ k) (hy : y ≠ k) (heq : skipFin k x hx = skipFin k y hy) : x = y := by
  have hval := congrArg Fin.val heq
  simp only [skipFin] at hval
  by_cases h1 : x.val < k.val <;> by_cases h2 : y.val < k.val <;> simp [h1, h2] at hval
  · exact Fin.ext hval
  · have hyne : y.val ≠ k.val := fun hv => hy (Fin.ext hv)
    omega
  · have hxne : x.val ≠ k.val := fun hv => hx (Fin.ext hv)
    omega
  · have hxne : x.val ≠ k.val := fun hv => hx (Fin.ext hv)
    have hyne : y.val ≠ k.val := fun hv => hy (Fin.ext hv)
    exact Fin.ext (by omega)

/-- Finite pigeonhole principle: any map `Fin (n + 1) → Fin n` collides at distinct indices. -/
theorem fin_pigeonhole :
    ∀ (n : Nat) (f : Fin (n + 1) → Fin n),
      ∃ i j : Fin (n + 1), i.val < j.val ∧ f i = f j
  | 0, f => (f ⟨0, Nat.zero_lt_succ 0⟩).elim0
  | n + 1, f => by
    let last : Fin (n + 2) := ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
    letI : Decidable (∃ i : Fin (n + 1), f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = f last) :=
      decExistsFin (n + 1) (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = f last)
    if hlast : ∃ i : Fin (n + 1), f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = f last then
      obtain ⟨i, hi⟩ := hlast
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, last, i.isLt, hi⟩
    else
      have hne : ∀ i : Fin (n + 1), f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≠ f last :=
        fun i hi => hlast ⟨i, hi⟩
      let g : Fin (n + 1) → Fin n := fun i =>
        skipFin (f last) (f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (hne i)
      obtain ⟨i, j, hij, hfg⟩ := fin_pigeonhole n g
      have hfi : f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ :=
        skipFin_inj (hne i) (hne j) hfg
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, hij, hfi⟩

end HJBrigade
