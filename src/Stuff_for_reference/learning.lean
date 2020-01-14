-- Tactics

-- intros is the plural of intro
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

-- show what simp did
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



