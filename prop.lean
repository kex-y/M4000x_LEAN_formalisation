import tactic.ring
import tactic.linarith
import tactic.library_search

-- Testing ground for theorems

theorem contrapositive
    (P Q : Prop) (HPQ : P → Q) : ¬ Q → ¬ P :=
begin
    intro HnQ,
    intro HP,
    apply HnQ,
    exact HPQ HP,
end

theorem and_transitive (P Q R : Prop) :
(P ∧ Q) ∧ (Q ∧ R) → (P ∧ R) :=
begin
  intro HPQQR,
  cases HPQQR with HPQ HQR,
  split,
  cases HPQ with HP HQ,
  exact HP,
  cases HQR with HQ HR,
  exact HR,
end

theorem iff_symmetric
    (P Q : Prop) : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intro HPQ,
  split,
  intro HQ,
  cases HPQ with HPQ' HQP',
  exact HQP'(HQ),
  intro HP,
  cases HPQ with HPQ' HQP',
  exact HPQ'(HP),
  intro HQP,
  split,
  cases HQP with HQP' HPQ',
  intro HP,
  exact HPQ'(HP),
  cases HQP with HQP' HPQ'
  intro HQ,
  exact HQP',
end

theorem iff_symmetry
  (P Q : Prop) : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intro HPQ,
  cases HPQ with HP HQ,
  split,
  exact HQ,
  exact HP,
  intro HQP,
  cases HQP with HQ HP,
  split,
  exact HP,
  exact HQ,
end

theorem iff_transitivity
  (P Q R : Prop) : (P ↔ Q) ∧ (Q ↔ R) → (P ↔ R) :=
begin
  intro HQQR,
  split,
  cases HQQR with HPQ HQR,
  cases HPQ with HP HQ0,
  cases HQR with HQ1 HR,
  intro P,
  exact HQ1(HP P),
  cases HQQR with HPQ HQR,
  cases HQR with HQ0 HR,
  cases HPQ with HP HQ1,
  intro R,
  exact HQ1(HR R),
end

theorem iff_transitivity_rw
  (P Q R : Prop) : (P ↔ Q) ∧ (Q ↔ R) → (P ↔ R) :=
begin
  intro HPQQR,
  cases HPQQR with HPQ HQR,
  rw HPQ,
  exact HQR,
end

theorem not_not'
  (P : Prop) : ¬ (¬ P) → P :=
begin
  cases(classical.em P) with HP HnP,
  intro HnnP,
  exact HP,
  intro HnnP,
  exfalso,
  exact HnnP HnP,
end

theorem contra 
  (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=
begin
  intro HnQnP,
  cases(classical.em Q) with HQ HnQ,
  intro HP,
  exact HQ,
  intro HP,
  exfalso,
  apply HnQnP,
  exact HnQ,
  exact HP,
end

theorem carried (P Q R : Prop) : (P → Q) ∧ (Q → R) → (P → R) := 
begin
  intro HPQQR,
  cases HPQQR with HPQ HQR,
  intro HP,
  exact HQR (HPQ HP),
end

example 
  (X : Type) (P Q : X → Prop) (a : X) (HP : ∀ x : X, P x) (HQ : ∀ x : X, Q x): P a ∧ Q a :=
begin
  have HPa : P a := HP a,
  have HQa : Q a,
    apply HQ,
  split,
  exact HPa,
  exact HQa,
end

example (P Q : Prop) : ¬ P → ¬ (P ∧ Q) :=
begin
  intro HnP,
  intro HPQ,
  cases HPQ with HP HQ,
  exact HnP HP,
end

example
  (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
  split,
    intro HPQR,
      cases HPQR with HP HQR,
      cases HQR with HQ HR,
        left,
        split,
        exact HP,
        exact HQ,
        right,
        split,
        exact HP,
        exact HR,
    intro HPQPR,
      cases HPQPR with HPQ HPR,
        cases HPQ with HP HQ,
        split,
        exact HP,
        left,
        exact HQ,
        cases HPR with HP HR,
        split,
        exact HP,
        right,
        exact HR,
end

example
    (P Q : Prop) : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q :=
begin
    intro HnPQ,
    cases(classical.em P) with HP HnP,
    right,
    intro HQ,
    have HPQ : P ∧ Q,
    split,
    exact HP,
    exact HQ,
    exact HnPQ HPQ,
    left,
    exact HnP,
end

example
  (P Q : Prop) : ¬ (P ∧ ¬ Q) → (P → Q) :=
begin
  intro HPnQ,
  cases(classical.em Q) with HQ HnQ,
  intro HP,
  exact HQ,
  intro HP,
  have HPQ : P ∧ ¬ Q,
  split, exact HP, exact HnQ,
  exfalso, exact HPnQ HPQ,
end

example
  (P Q : Prop) : ¬ (P → Q) → (P ∧ ¬ Q) :=
begin
  intro h,
  split, -- ¬ in hypothesis → use excluded middle on goal
  cases (classical.em P) with hp hnp,
  exact hp, -- exact the correct and exfalso the incorrect
  have hnqp : ¬ Q → ¬ P, intro, exact hnp,
  have hpq : P → Q, intro hp, exfalso, exact hnp hp,
  exfalso, exact h hpq,
  cases (classical.em Q) with hq hnq,
  have hpq : P → Q, intro, exact hq,
  exfalso, exact h hpq,
  exact hnq,
end

example
  (P Q : Prop) : (P ∧ ¬ Q) → ¬ (P → Q) :=
begin
  intro h,
  have hp : P, exact h.left,
  have hnq : ¬ Q, exact h.right,
  cases (classical.em (P → Q)) with hpq hnpq,
  have hq : Q, exact hpq hp,
  exfalso, exact hnq hq,
  exact hnpq,
end

variables p q r : Prop

example : p ∨ q → q ∨ p :=
begin
  intro h,
  cases h with hp hq,
  right, exact hp,
  left, exact hq,
end

example : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
begin
  intro h,
  cases h with hp hqr,
  left, left, exact hp,
  cases hqr with hq hr,
  left, right, exact hq,
  right, exact hr,
end

example : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  split, exact hq, exact hp,
end

example : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
begin
  intro h,
  cases h with hp hqr,
  cases hqr with hq hr,
  repeat {split},
  exact hp, exact hq, exact hr,
end

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  split,
    intro h0,
    cases h0 with hp hqr,
    cases hqr with hq hr,
    left, split, exact hp, exact hq,
    right, split, exact hp, exact hr,
    intro h1,
    cases h1 with hpq hpr,
    cases hpq with hp hq,
    split, exact hp, left, exact hq,
    cases hpr with hp hr,
    split, exact hp, right, exact hr,
end

example : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q :=
begin
  split,
  intro h0,
  cases (classical.em p),
  right, intro h1,
  have h2: p ∧ q, split, exact h, exact h1,
  exact h0 h2,
  left, exact h,
  intro h0,
  cases h0 with hnp hnq,
  intro x, cases x with hp hq,
  exact hnp hp,
  intro x, cases x with hp hq,
  exact hnq hq,
end

example : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
begin
  split, intro h, split, 
  intro hp,
  have hpq : p ∨ q, left, exact hp,
  exact h hpq,
  intro hq,
  have hpq : p ∨ q, right, exact hq,
  exact h hpq,
  intro h, cases h with hnp hnq,
  intro hpq,
  cases hpq, exact hnp hpq, exact hnq hpq,
end

example : ¬ (p ↔ ¬ p) :=
begin
  intro h,
  cases h with h0 h1,
  cases (classical.em p),
  have hnp : ¬ p, exact h0 h,
  exact hnp h,
  have hp : p, exact h1 h,
  exact h hp,
end

example : p ∨ ¬ p :=
begin
  cases (classical.em p),
  left, exact h,
  right, exact h,
end

example : (p → q) ↔ (¬ q → ¬ p) :=
begin
  split,
  intro h, intro hq,
  cases (classical.em p),
  exfalso, exact hq (h h_1),
  exact h_1,
  intro h, intro hp,
  cases (classical.em q),
  exact h_1,
  exfalso, exact (h h_1) hp,
end

variables (X : Type) (P Q : X → Prop)

example : (∀ x, P x ∧ Q x) → (∀ x, Q x ∧ P x) :=
begin
  intro h,
  intro x,
  have hpq : P x ∧ Q x:= h x,
  cases hpq with hp hq,
  split, exact hq, exact hp,
end

example : (∃ x, P x ∨ Q x) → (∃ x, Q x ∨ P x) :=
begin
  intro h,
  cases h with x Hx,
  cases Hx with HPx HQx,
  have HPQ : Q x ∨ P x, right, exact HPx,
  existsi x, exact HPQ,
  have HPQ : Q x ∨ P x, left, exact HQx,
  existsi x, exact HPQ, 
end

example : (∀ x, P x) ∧ (∀ x, Q x) ↔ (∀ x, P x ∧ Q x) :=
begin
  split,
  intro h,
  cases h with HPx HQx,
  intro x,
  have HP : P x, exact HPx x,
  have HQ : Q x, exact HQx x,
  split, exact HP, exact HQ,
  intro h,
  split,
  intro x,
  have HPQ : P x ∧ Q x, exact h x,
  cases HPQ with HP HQ, exact HP,
  intro x,
  have HPQ : P x ∧ Q x, exact h x,
  cases HPQ with HP HQ, exact HQ,
end

example : (∃ x, P x) ∨ (∃ x, Q x) ↔ (∃ x, P x ∨ Q x) :=
begin
  split,
  intro h,
  cases h with HPx HQx,
  cases HPx with x HP,
  have HPQ : P x ∨ Q x, left, exact HP,
  existsi x, exact HPQ,
  cases HQx with x HQ,
  have HPQ : P x ∨ Q x, right, exact HQ,
  existsi x, exact HPQ,
  intro h,
  cases h with x HPQ,
  cases HPQ with HP HQ,
  left, existsi x, exact HP,
  right, existsi x, exact HQ,
end

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x  :=
begin
    intro h,
    intro hx,
    have hpq : p hx ∧ q hx,
    exact h hx,
    cases hpq,
    exact hpq_left,
end

example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  split,
  intro h,  
  apply classical.by_contradiction,
  intro h2,
  apply h, intro x,
  have nnP : ¬ ¬ P x,
  intro hNpx,
  apply h2,
  existsi x,
  exact hNpx,
  apply classical.by_contradiction,
  intro h3,
  exact nnP h3,

  intro h,
  intro h1,
  cases h with x np,
  have hp : P x, apply h1,
  exact np hp,
end

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
  rw hc,
  rw mul_assoc,
  rw mul_assoc,
  rw hc,
  rw mul_left_comm,
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
begin
  exact (mul_lt_mul_right h).mpr,
end

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

example (P : Prop) : ¬ (¬ P) → P :=
begin
  intro h,
  apply classical.by_cases,
  cc, cc, exact P,
end

example (P Q : Prop) : ¬ (¬ P ∧ ¬ Q) → P ∨ Q :=
begin
  push_neg,
  intro, assumption,
end

example (P Q :Prop) : (P → Q) → (¬ P ∨ Q) :=
begin
  intro h,
  cases classical.em P with hp hnp,
  right,
  exact h hp,
  left,
  assumption,
end

theorem wellordered
  (S : set ℕ) : S ≠ ∅ → ∃ s ∈ S, ∀ x ∈ S, s ≤ x :=
begin
  intro nempty,
  apply classical.by_contradiction,
  push_neg,
  intro h,

  have empty: ∀ n : ℕ, n ∉ S,
    intro x,
    induction x with hb hsucc,
    

end

example (a b : ℕ) : a + a = b + b → a = b :=
begin
  ring,
  rw nat.mul_left_inj,
  intro, assumption,
  simp,
end
