-- begin header
import tactic.ring
import data.rat.basic
import data.rat.cast
import tactic.linarith
import tactic.norm_cast

namespace M40001
-- end header

/- Section
1.3 Relations
-/

/- Sub-section 
1.3.1 The Law of the Excluded Middle
-/

/-
The Law of the Excluded Middle states that for any proposition $P$, either $P$, or its negation $¬ P$ is true.
-/

/- Theorem
If $P$ is a proposition, then $ ¬ (¬ P) ⇔ P$.
-/
theorem not_not_P_is_P
    (P : Prop) : ¬ (¬ P) ↔ P :=
begin
    -- We need to show that $¬ (¬ P)$ is true 'if and only if' $P$ is true. So we consider both directions of the implication.
    split,
    -- Let's first consider the forward implication, i.e. $¬ (¬ P)$ is true implies that $P$ is also true.
    intro hp,
    -- We will prove this by contradiction so given $¬ (¬ P)$ is true let's make a dubious assumption that $¬ P$ is true.
    apply classical.by_contradiction,
    intro hnp,
    -- But $¬ P$ is true implies that $¬ (¬ P)$ is false which is a contradiction to our premis that $¬ (¬ P)$ is true. Thus, $¬ P$ must be false which by the Law of the excluded middle implies $P$ is true, resulting in the first part of the proof!
    contradiction,
    -- Now we need to proof that the backwards implication is also correct, i.e. $P$ is true implies $¬ (¬ P)$ is also true.
    -- To show that $¬ (¬ P)$ is true when $P$ is true, we can simply show that $P$ is true implies $¬ P$ is false.
    intros hp hnp,
    contradiction,
    -- But this is true by definition, so we have nothing left to prove!
end

/- Sub-section
1.3.2 De Morgan's Laws
-/

/- Theorem
(1) Let $P$ and $Q$ be propositions, then $¬ (P ∨ Q) ⇔ (¬ P) ∧ (¬ Q)$
-/
theorem demorgan_a
    (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬ P) ∧ (¬ Q) :=
begin
    -- Again we have an 'if and only if' statement so we need to consider both directions of the argument.
    split,
    -- We first show that $¬ (P ∨ Q) ⇒ ¬ P ∧ ¬ Q$ through contradiction. Suppose $¬ (P ∨ Q)$ is true, and we make a dubious assumption that $P$ is true.
    intro h,
    split,
    intro hp,
    -- But then $¬ (P ∨ Q)$ is false! A contradiction! Therefore $P$ must be false.
    apply h,
    left, exact hp,
    -- Similarly, supposing $Q$ is true also results in a contradiction! Therefore $Q$ is also false. 
    intro hq,
    apply h,
    right, exact hq,
    -- With that, we now focus our attention on the backwards implication, i.e. $(¬ P) ∧ (¬ Q) ⇒ ¬ (P ∨ Q)$.
    -- Again, let's approach this by contradiction. Given $¬ P ∧ ¬ Q$ suppose we have $P$ or $Q$.
    intros h hpq,
    -- But $P$ can't be true, as we have $¬ P$,
    cases h with hnp hnq,
    cases hpq with hp hq,
    contradiction, 
    -- Therefore, $Q$ must be true.
    -- But $Q$ also can't be true as we have $¬ Q$! Contradiction!
    contradiction,
    -- Therefore, given $(¬ P) ∧ (¬ Q)$, $(P ∨ Q)$ must not be true, i.e. $¬ (P ∨ Q)$ is true, which is exactly what we need!
end

/- Theorem
(2) Let $P$ and $Q$ be propositions, then $¬ (P ∧ Q) ⇔ (¬ P) ∨ (¬ Q)$
-/
theorem demorgan_b
    (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P) ∨ (¬ Q) :=
begin
    -- Once again, we have an 'if and only' if statement, therefore, we need to consider both directions. 
    split,
    -- We first show that $¬ (P ∧ Q) ⇒ ¬ P ∨ ¬ Q$. Suppose $¬ (P ∧ Q)$.
    intro h,
    -- By the law of the excluded middle, we have either $P$ or $¬ P$.
    cases (classical.em P) with hp hnp,
    -- Suppose first that we have $P$. Then, we must have $¬ Q$ as having $Q$ implies $P ∧ Q$ which contradicts with $¬ (P ∧ Q)$,
    have hnq : ¬ Q,
        intro hq,
        have hpq : P ∧ Q,
            split, exact hp, exact hq,
        contradiction,
    -- hence, we have $¬ P ∨ ¬ Q$.
    right, exact hnq,
    -- Now let's suppose $¬ P$. But as $¬ P$ implies $¬ P ∨ ¬ Q$, we have nothing left to prove.
    left, exact hnp,
    -- With the forward implication dealt with, let's consider the reverse, i.e. $¬ P ∨ ¬ Q ⇒ ¬ (P ∧ Q)$.
    -- Given $¬ P ∨ ¬ Q$ let's suppose that $P ∧ Q$.
    intros h hpq,
    -- But this is a contradiction as $P ∧ Q$ implies that neither $P$ nor $Q$ is false!
    cases h with hnp hnq,
        cases hpq with hp hq,
        contradiction,
        cases hpq with hp hq,
        contradiction,
    -- Therefore, $P ∧ Q$ must be false by contradiction which results in the second part of our proof!
end

/- Sub-section
1.3.3 Transitivity of Implications, and the Contrapositive
-/

/- Theorem
$⇒$ is transitive, i.e. if $P$, $Q$, and $R$ are propositions, then $P ⇒ Q$ and $Q ⇒ R$ means $P ⇒ R$.
-/
theorem imp_trans
    (P Q R : Prop) : (P → Q) ∧ (Q → R) → (P → R) :=
begin
    -- Suppose $P ⇒ Q$ and $Q ⇒ R$ are both true, we then would like to prove that $P ⇒ R$ is true.
    intro h,
    cases h with hpq hqr,
    -- Say that $P$ is true,
    intro hp,
    -- then by $P ⇒ Q$, $Q$ must be true. But we also have $Q ⇒ R$, therefore $R$ is also true, which is exactly what we wish to prove!
    exact hqr (hpq hp),
end

/- Theorem
If $P$ and $Q$ are propositions, then $(P ⇒ Q) ⇔ (¬ Q ⇒ ¬ P)$.
-/
theorem contra
    (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
    -- Let's first consider the implication from left to right, i.e. $(P ⇒ Q) ⇒ (¬ Q ⇒ ¬ P)$.
    split,
    -- We will prove this by contradiction, so suppose we have $P ⇒ Q$, $¬ Q$ and not $¬ P$. 
    intros h hnq hp,
    -- But not $¬ P$ is simply $P$, and $P$ implies $Q$, a contradiction to $¬ Q$! Therefore, $P ⇒ Q$ must imply $¬ Q ⇒ ¬ P$ as required.
    exact hnq (h hp),
    -- Now lets consider reverse, $(¬ Q ⇒ ¬ P) ⇒ (P ⇒ Q)$. Suppose we have $¬ Q ⇒ ¬ P$ and $P$.
    intros h hp,
    -- If $Q$ is true then we have nothing left to prove, so suppose $¬ Q$ is true.
    cases (classical.em Q) with hq hnq,
    exact hq,
    exfalso,
    -- But $¬ Q$ implies $¬ P$ which contradicts with $P$, therefore, $¬ Q$ must be false as requied.
    exact h hnq hp,
end

/- Sub-section
1.3.4 Distributivity
-/

/- Theorem
(1) If $P$, $Q$, and $R$ are propositions. Then, $P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)$;
-/
theorem dis_and_or
    (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
    -- Let's first consider the foward implication, $P ∧ (Q ∨ R) ⇒ (P ∧ Q) ∨ (P ∧ R)$
    split,
    -- Suppose $P$ is true and either $Q$ or $R$ is true.
    rintro ⟨hp, hqr⟩,
    -- But this means either $P$ and $Q$ is true or $P$ and $R$ is true which is exactly what we need.
    cases hqr with hq hr,
    left, split, repeat {assumption},
    right, split, repeat {assumption},
    -- With that, we now need to prove the backwards implication. Suppose $(P ∧ Q) ∨ (P ∧ R)$.
    intro h,
    -- Let's consider both cases.
    cases h with hpq hpr,
    -- If $P ∧ Q$ is true, then $P$ is true and $Q ∨ R$ is also true.
    cases hpq with hp hq,
    split, assumption, left, assumption,
    -- Similarly, is $P ∧ R$ is true, then $P$ is true and $Q ∨ R$ is also true. 
    cases hpr with hp hr,
    split, assumption, right, assumption,
    -- Therefore, by considering bothe cases, we see that either $P ∧ Q$ or $P ∧ R$ implies $P ∧ (Q ∨ R)$.
end

/- Theorem
(2) $P ∨ (Q ∧ R) ⇔ (P ∨ Q) ∧ (P ∨ R)$.
-/
theorem dis_or_and
    (P Q R : Prop) : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
begin
    -- We first consider the forward implication $P ∨ (Q ∧ R) ⇒ (P ∨ Q) ∧ (P ∨ R)$.
    split,
    -- Suppose we have $P ∨ (Q ∧ R)$, then either $P$ is true or $Q$ and $R$ is true$.
    intro h,
    -- Let's consider both cases. If $P$ is true, then both $P ∨ Q$ and $P ∨ R$ are true.
    cases h with hp hqr,
    split, repeat {left, assumption},
    -- Similarly, if $P$ and $Q$ are true, then both $P ∨ Q$ and $P ∨ R$ are true. 
    cases hqr with hq hr,
    split, repeat {right, assumption},
    -- Now let's consider the backwards implication. Suppose that $(P ∨ Q)$ and $(P ∨ R)$ is true and lets consider all the cases.
    intro h,
    cases h with hpq hpr,
    -- If $P$ is true the $P ∨ (Q ∧ R)$ is also true.
    cases hpq with hp hq,
    cases hpr with hp hr,
    repeat {left, assumption},
    -- If $¬ P$ is true then from $(P ∨ Q)$ and $(P ∨ R)$, $Q$ and $R$ must be true, and therefore, $P ∨ (Q ∧ R)$ is also true.
    cases hpr with hp hr,
    left, assumption,
    right, split, repeat {assumption},
end

/- Section
1.4 An Application
-/

/- 
We would like prove that there is no rational number whose square is 2 using the techniques introduced earlier.
-/

-- Section moved to Sqrt2_not_rational.lean

end M40001
