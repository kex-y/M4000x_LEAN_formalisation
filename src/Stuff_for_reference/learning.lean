import data.real.basic

-- Tactics
-- revert is kinda the inverse of intro

example (x : ℕ) : x = x :=
begin
  revert x,
  -- goal is ⊢ ∀ (x : ℕ), x = x
  intro y,
  -- goal is y : ℕ ⊢ y = y
  reflexivity
end

-- arbitary expressions can be generalized using genralize

example : 3 = 3 :=
begin
  generalize : 3 = x,
  -- goal is x : ℕ ⊢ x = x,
  revert x,
  -- goal is ⊢ ∀ (x : ℕ), x = x
  intro y, reflexivity
end

-- use this when confused
-- set_option pp.notation false

-- shows what simp did
-- set_option trace.simplify.rewrite true

example (p q : Prop) : p → q → p := λ hp, λ hq, hp

example (p q r s : Prop) (h₁ : q → r) (h₂ : p → q) : p → r := λ hp : p, h₁ (h₂ hp)
example (p q r s : Prop) (h₁ : q → r) (h₂ : p → q) : p → r :=
assume hp : p,
show r, from h₁ (h₂ hp)

example (p q : Prop) : p → q → p ∧ q :=
assume hp : p,
assume hq : q,
show p ∧ q, from and.intro hp hq
example (p q : Prop) : p → q → p ∧ q := λ hp : p, λ hq : q, ⟨hp, hq⟩ -- or we can use and.intro hp hq

example (p q : Prop) (h : p ∧ q) : p := h.left -- or and.elim_left h

example (p q : Prop) : p ∧ q → q ∧ p := λ h : p ∧ q, and.intro h.right h.left

example (p q : Prop) : p → p ∨ q := λ hp : p, or.intro_left q hp

example (p q : Prop) : p ∨ q → q ∨ p := 
λ h : p ∨ q, or.elim h (λ hp : p, show q ∨ p, from or.inr hp) (λ hq : q, show q ∨ p, from or.inl hq)

example (p q : Prop) : (p → q) → ¬ q → ¬ p :=
λ h : p → q, λ hnq : ¬ q, λ hp : p, show false, from hnq (h hp)

example (p q r : Prop) : ¬ p → q → (q → p) → r :=
assume hnp : ¬ p,
assume hq : q,
assume h : q → p,
absurd (h hq) hnp

example (p q : Prop) : p ∧ q ↔ q ∧ p :=
iff.intro
    (assume hpq : p ∧ q, ⟨hpq.right, hpq.left⟩)
    (assume hqp : q ∧ p, ⟨hqp.right, hqp.left⟩)

inductive names : Type
| Johanson : names
| Kristian : names
| Marlin : names
| Maria : names
| NoOne : names

namespace names
  #check Maria

  def age_of_person (person : names) : ℕ :=
  names.cases_on person 18 19 18 23 99999

  #reduce age_of_person Maria

  def next_person (person : names) : names :=
  names.rec_on person Kristian Marlin Maria NoOne Johanson

end names

namespace hidden

  inductive nat
  | zero : nat
  | succ (n : nat) : nat

  namespace nat

    def add : nat → nat → nat
    | m zero := m
    | m (succ n) := succ (add m n)

    notation m ` + ` n := add m n

    def mul : nat → nat → nat
    | m zero := zero
    | m (succ n) := add (mul m n) m

    notation m ` × ` n := mul m n

    theorem add_zero (x : nat) : x + zero = x := rfl

    theorem add_succ (x y : nat) : x + succ y = succ (x + y) := rfl

    theorem add_assoc (x y z : nat) : (x + y) + z = x + (y + z) :=
    begin
      induction z with k hk,
        repeat {rw add_zero},
        repeat {rw add_succ},
        rw hk
    end

    theorem zero_add (x : nat) : zero + x = x :=
    begin
      induction x with k hk,
        rw add_zero,
        rw [add_succ, hk]
    end

    theorem succ_add (x y : nat) : (succ x) + y = succ (x + y) :=
    begin
      induction y with k hk,
        repeat {rw add_zero},
        rw [add_succ, hk, add_succ]
    end

    theorem add_comm (x y : nat) : x + y = y + x :=
    begin
      induction y with k hk,
        rw [add_zero, zero_add],
        rw [add_succ, succ_add, hk]
    end
  end nat

  universes u v

  inductive sum (α : Type u) (β : Type v)
  | inl {} : α → sum
  | inr {} : β → sum

  variable {α : Type u}

end hidden

example (F G H : Type → Prop) (h : ∀ x : Type, (F x → (¬ G x → H x))) : ∀ x : Type, (F x → (G x ∨ H x)) :=
begin
  intros x hF, -- So I'm fixing x and supposing F x is true. We now need to show G x ∨ H x
  cases classical.em (G x) with hG hG, -- By excluded middle (I assume we can use classical logic since we are not cs?) either G x is true or its false
  left, from hG, -- If G x is true than G x ∨ H x is true so we are done!
  right, from h x hF hG -- If G x is false then as from assumption (h : ∀ x : Type, (F x → (¬ G x → H x))), we have not G x implies H x is true so G x or H x is true!
end

example (F G H : Type → Prop) (h : ∀ x : Type, (F x → (¬ G x → H x))) : ∀ x : Type, (F x → (G x ∨ H x)) :=
begin
  finish
end