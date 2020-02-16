import tactic.ring
import tactic.linarith

-- Testing ground for theorems

theorem contrapositive
  (P Q : Prop) (HPQ : P → Q) : ¬ Q → ¬ P :=
by {intros hnq hp, from hnq (HPQ hp)}

theorem and_transitive (P Q R : Prop) :
  (P ∧ Q) ∧ (Q ∧ R) → (P ∧ R) :=
by {intro h, from ⟨h.left.left, h.right.right⟩}

theorem iff_symmetric
    (P Q : Prop) : (P ↔ Q) ↔ (Q ↔ P) :=
by {split,
  {intro h, rw h},
  {intro h, rw h}
}

example
  (P Q R : Prop) : (P ↔ Q) ∧ (Q ↔ R) → (P ↔ R) :=
by {
  intro h, split,
  {intro hp, rwa [←h.right, ←h.left]},
  {intro hr, rwa [h.left, h.right]}
}

example
  (P : Prop) : ¬ (¬ P) ↔ P :=
by {
  split,
  {intro h, 
  cases classical.em P,
    {assumption},
    {contradiction} },
  {intros hp hnp, contradiction}
}

example
  (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=
by {
  intros h hp,
  apply classical.by_contradiction,
  intro hnq,
  from (h hnq) hp
}


example (P Q R : Prop) : (P → Q) ∧ (Q → R) → (P → R) := 
by {intros h hp, from h.right (h.left hp)}

example 
  (X : Type) (P Q : X → Prop) (a : X) (HP : ∀ x : X, P x) (HQ : ∀ x : X, Q x): P a ∧ Q a :=
by {from ⟨HP a, HQ a⟩}

example (P Q : Prop) : ¬ P → ¬ (P ∧ Q) :=
by {intro h, push_neg, left, assumption}

example
  (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
by {
  split,
  {intro h, cases h.right with Q R,
  all_goals { {left, from ⟨h.left, Q⟩}  <|> {right, from ⟨h.left, R⟩} } },
  {intro h, cases h,
  all_goals {split, from h.left},
  {left, from h.right},
  {right, from h.right}  }
}

example
    (P Q : Prop) : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q :=
by {push_neg, intro, assumption}

example
  (P Q : Prop) : ¬ (P ∧ ¬ Q) → (P → Q) :=
by {
  push_neg, intros h hp, cases h, 
  {contradiction}, 
  {assumption}
}

example
  (P Q : Prop) : ¬ (P → Q) → (P ∧ ¬ Q) :=
by {push_neg, intro, assumption}

example
  (P Q : Prop) : (P ∧ ¬ Q) → ¬ (P → Q) :=
by {push_neg, intro, assumption}

variables p q r : Prop

example : p ∨ q → q ∨ p :=
by {intro h, cases h, all_goals{{left, assumption} <|> {right, assumption}}}

example : ¬ (p ↔ ¬ p) :=
by {
  intro h,
  cases classical.em p with hp hnp,
  {from (h.mp hp) hp},
  {from hnp (h.mpr hnp)}
}

example : p ∨ ¬ p :=
by {
  cases classical.em p,
  all_goals { {left, assumption} <|> {right, assumption} }
}

example : (p → q) ↔ (¬ q → ¬ p) :=
by {
  split,
  all_goals {intros a b},
  {intro h, from b (a h)},
  {apply classical.by_contradiction, intro h, from (a h) b}
}

variables (X : Type) (P Q : X → Prop)

example : (∀ x, P x ∧ Q x) → (∀ x, Q x ∧ P x) :=
by {
  intros h x,
  split, all_goals {  {from (h x).right} <|>  {from (h x).left} }
}

example : (∃ x, P x ∨ Q x) → (∃ x, Q x ∨ P x) :=
by {
  rintro ⟨x, hx⟩, existsi x,
  cases hx,
  all_goals { {left, assumption} <|> {right, assumption}}
}

example : (∀ x, P x) ∧ (∀ x, Q x) ↔ (∀ x, P x ∧ Q x) :=
by {
  split,
  {rintros ⟨hp, hq⟩ x, from ⟨hp x, hq x⟩},
  {intro h, split,
  all_goals {intro x, from (h x).left <|> from (h x).right} }
}

example : (∃ x, P x) ∨ (∃ x, Q x) ↔ (∃ x, P x ∨ Q x) :=
by {
  split,
  {intro h, repeat {rcases h with ⟨x, hx⟩},
  all_goals {existsi x, {left, assumption} <|> {right, assumption}  }
  },
  {rintro ⟨x, hx⟩, cases hx, 
  {left, existsi x, assumption},
  {right, existsi x, assumption} }
}

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x  :=
by {intros h x, from (h x).left}

example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
by {push_neg, refl}

def even (a : ℤ) := ∃ b : ℤ, a = 2 * b
def odd (a : ℤ) := ∃ b : ℤ, a = 2 * b + 1

theorem timeseven
  (a : ℤ) : even a → even (a * a) :=
begin
  intro h,
  have h1 : ∃ b : ℤ, a = 2 * b, exact h,
  have h2 : ∃ b : ℤ, a * a = 2 * b,
  cases h1 with hz ha,
  existsi 2 * hz * hz,
  rw ha,
  have hc : 2 * hz = hz * 2, 
    rw mul_comm,
  rw [hc, mul_assoc, mul_assoc, hc, mul_left_comm],
  exact h2,
end

theorem timesodd
  (a : ℤ) : odd a → odd (a * a) :=
begin
  intro h,
  have h1 : ∃ b : ℤ, a = 2 * b + 1, exact h,
  have h2 : ∃ b : ℤ, a * a = 2 * b + 1,
  cases h1 with x ha,
  existsi 2 * x * x + 2 * x,
  rw ha,
  ring,
  exact h2,
end 

theorem eventimesodd
  (a b : ℤ) : odd a ∧ even b → even (a * b) :=
begin
  intro h,
  cases h with ha hb,
  have h1 : ∃ c : ℤ, a = 2 * c + 1, exact ha,
  have h2 : ∃ c : ℤ, b = 2 * c, exact hb,
  have h3 : ∃ c : ℤ, a * b = 2 * c,
  cases h1 with x0 hk,
  cases h2 with x1 hm,
  existsi x1 * (2 * x0 + 1),
  rw hk, rw hm,
  ring,
  exact h3,
end

theorem orderx (x y z : ℕ) (h : z > 0) : x > y → x * z > y * z :=
by {from (mul_lt_mul_right h).mpr}

theorem orderone (a b : ℕ) (ha : a > 1) : b > 1 → a * b > a :=
begin
  intro h,
  have hb : b > 0,
    have h0 : 1 > 0,
      simp,
    exact trans h h0,
  have hc : a = a * 1, simp,
  rw hc,
  have hd : 1 * b = b, simp,
  rw mul_assoc,
  rw hd,
  rw mul_comm,
  have he : a * 1 = 1 * a, simp,
  rw he,
  apply orderx,
  have hf : 1 > 0, simp,
  exact trans ha hf,
  exact h,
end

theorem ordermul
  (a b n : ℕ) (h1 : a > 1) (h2 : b > 1): n > a * b → n > a ∧ n > b :=
begin
  intro h,
  split, 
  have hab : a * b > a,
    apply orderone, exact h1, exact h2,
  exact trans h hab,
  have hba : a * b > b,
    rw mul_comm, apply orderone, exact h2, exact h1,
  exact trans h hba,
end

example (P Q : Prop) : ((P → Q) → P) → P :=
begin
  intro h,
  cases classical.em P with hp hnp,
  assumption,

  have ha : ¬ P → ¬ (P → Q),
    apply contrapositive,
    assumption,
  have hb : ¬ (P → Q) := ha hnp,
  revert hb,
  push_neg,
  intro hc,
  exact hc.left,
end

example (a b : ℕ) : a + a = b + b → a = b :=
by{ring, rw nat.mul_left_inj, intro; assumption, simp}