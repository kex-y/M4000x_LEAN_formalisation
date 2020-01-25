-- begin header
import tactic.ring

namespace M40001
-- end header

/- Section
Chapter 1. Sets and Logic
-/

/- Sub-section
1.1 Proposition and logic
-/

/- Definition
A logical proposition, usually just called a proposition, is a true/false statement. 
In LEAN we say $P$ is a proposition if it has type Prop, and we write (P : Prop).
-/

/-
Some examples of logical propositions include:

$2 + 2 = 4.$

$2 + 2 = 5.$

For all real numbers $x$ and $y$, $x + y = y + x$.

The statement of Pythagoras' theorem.

The statement of the Riemann Hypothesis.
-/

/-
Each of these statements is either true, or false. In fact, the first, third and fourth statements are true, the second one is false, and nobody knows whether the last one is true or false.
-/

/-
Here are some examples of mathematical objects which are not propositions:

$2 + 2$

$+$

$\pi$

The proof of Pythagoras' theorem.
-/

/-
None of these are true/false statements. The first and third of them are numbers, the second one is a function (which takes two numbers $a$ and $b$ in and outputs their sum $a+b$), and the last one is a proof, which is a sequence of logical arguments.
-/

/- Sub-section
1.2 Doing mathematics with propositions
-/

/-
You all know that if you want to do mathematics with a general real number, you can just call it $x$. Then you can talk about things like $x-3$ or $x^2+2x+1$ and so on. You can also do mathematics with matrices; you can let $A$ and $B$ be general two by two matrices, and then talk about things like $A+B$.
-/

/-
During your degree here, you will learn that you can also do mathematics with some far more general things. You will do mathematics with numbers, matrices, groups, elements of groups, rings, elements of rings, vector spaces, elements of vector spaces and so on. In this section, we will do mathematics with propositions.
-/

/-
If you're doing mathematics with real numbers like $x$ and $y$, you can do things like considering $x+y$ (a number) or $x^2/y$ (a number, as long as $y$ isn't zero), or $x=y$ (a proposition), or $x<y$ (a proposition).
-/

/-
If you're doing mathematics with propositions, there are different things you can do. In this section we will see the most important things we can do with propositions.
-/

/- Sub-section
1.2.1 And ($∧$)
-/

/-
Good variable names for propositions are things like $P$ or $Q$ or $R$.
-/

/-
If $P$ and $Q$ are propositions, we can make a new proposition called $P∧ Q$. The symbol $∧$ is pronounced ``and''. The definition of $P ∧ Q$ is that $P ∧ Q$ is true if, and only if, both $P$ and $Q$ are true.
-/

/-
Unlike number variables like $x$, proposition variables like $P$ can only take two values - true and false. So we can explain precisely what $P ∧ Q$ is by writing down the so-called truth table for $∧$:
-/



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
    -- But this is true by definition, so we have nothing left to prove!
    contradiction,
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
    -- But $Q$ also can't be true as we have $¬ Q$! Contradiction! Therefore, given $(¬ P) ∧ (¬ Q)$, $(P ∨ Q)$ must not be true, i.e. $¬ (P ∨ Q)$ is true, which is exactly what we need!
    contradiction,
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
    -- Therefore, $P ∧ Q$ must be false by contradiction which results in the second part of our proof!
        contradiction,
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
    -- Therefore, by considering bothe cases, we see that either $P ∧ Q$ or $P ∧ R$ implies $P ∧ (Q ∨ R)$.
    split, assumption, right, assumption,
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

end M40001
