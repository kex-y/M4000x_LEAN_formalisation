-- begin header
import tactic.ring

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
    -- But this is true by definition, so we have nothing left to prove!
    contradiction,
end

/-
Remark. Note that for many simple propositions alike the one above, LEAN is able to use automation to complete our proof. Indeed, by using the tactic $\tt{finish}$, the above proof becomes a one-liner!
-/

/- Theorem
If $P$ is a proposition, then $ ¬ (¬ P) ⇔ P$. (This time proven using $\tt{finish}$)
-/
theorem not_not_P_is_P_tauto
    (P : Prop) : ¬ (¬ P) ↔ P :=
begin
    -- As we can see, $\tt{finish}$ finished the proof!
    finish
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

/-
Excercise. As you can see, writing LEAN proofs is so much more fun than drawing truth tables! Why don't you try it out by proving $\lnot P \iff (P \implies \tt{false})$ <a href="https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FJasonKYi%2FM4000x_LEAN_formalisation%2Fmaster%2Fhtml%2FExercises%2FExercies1.lean">here</a>?
-/

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

/-
Excercise. What can we deduce if we apply the contrapositive to $\lnot Q \implies \lnot P$? Try it out <a href="https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FJasonKYi%2FM4000x_LEAN_formalisation%2Fmaster%2Fhtml%2FExercises%2FExercies2.lean">here</a>?
-/

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

/- Section
1.7 Sets and Propositions
-/

universe u
variable {Ω : Type*}

-- Let $Ω$ be a fixed set with subsets $X$ and $Y$, then

/- Theorem
(1) $\bar{X ∪ Y} = \bar{X} ∩ \bar{Y}$.
-/
theorem de_morg_set_a (X Y : set Ω) : - (X ∪ Y) = - X ∩ - Y :=
begin
    -- What exactly does $\bar{(X ∪ Y)}$ and $\bar{X} ∩ \bar{Y}$ mean? Well, lets find out!
    ext,
    -- As we can see, to show that $\bar{X ∪ Y} = \bar{X} ∩ \bar{Y}$, we in fact need to prove $x ∈ \bar{(X ∪ Y)} ↔ x ∈ \bar{X} ∩ \bar{Y}$.
    split,
    -- So let's first prove that $x ∈ \bar{X ∪ Y} → x ∈ \bar{X} ∩ \bar{Y}$. Suppose $x ∈ \bar{X ∪ Y}$, then $x$ is not in $X$ and $x$ is not in $Y$.
    dsimp, intro h,
    push_neg at h,
    -- But this is exactly what we need!
    assumption,
    -- Now, let's consider the backwards implication. Similarly, $x ∈ \bar{X} ∩ \bar{Y}$ means $x$ is not in $X$ and $x$ is not in $Y$.
    dsimp, intro h,
    -- But this is what $x ∈ \bar{X ∪ Y}$ means, so we're done!
    push_neg,
    assumption
    
end

/- Theorem
(2) $\bar{X ∩ Y} = \bar{X} ∪ \bar{Y}$.
-/
theorem de_morg_set_b (X Y : set Ω) : - (X ∩ Y) = - X ∪ - Y :=
begin
    -- Rather than proving this manually, why not try some automation this time.
    ext, finish
end

/-
Remark. Would you look at that! Proving the de Morgan's law with one single line. Now thats a nice proof if I ever seen one!
-/

/- Sub-section
1.7.1 "For All" and "There Exists"
-/

/- Theorem
Given a propositon $P$ whose truth value is dependent on $x ∈ X$, then $∀ x ∈ X, ¬ P(x) ⇔ ¬ (∃ x ∈ X, P(x))$, and
-/
theorem neg_exist_is_all (X : Type) (P : X → Prop) : (∀ x : X, ¬ P x) ↔ ¬ (∃ x : X, P x) :=
begin
    -- (⇒) Let's first prove the forward implication, i.e. suppose that $∀ x ∈ X, ¬ P(x)$, we need to show that $¬ ∃ x ∈ X, P(x)$.
    split,
    -- Let's prove this by contradiction! Let's suppose that $¬ ∃ x ∈ X, P(x)$ is in fact $\tt{false}$ and there is actually a $x$ out there where $P(x)$ is true!
    rintro h ⟨x, hx⟩,
    -- But, by our assumption $∀ x ∈ X$, $P(x)$ is false, thus a contradiction! 
    from (h x) hx,
    -- (⇐) Now let's consider the other direction. Suppose that there does not exist a $x$ such that $P(x)$ is true, i.e. $¬ ∃ x ∈ X, P(x)$.
    intro ha,
    -- Similarly, let's suppose that $∀ x ∈ X, ¬P x$ is not true.
    intros x hx,
    -- But then, there must be a $x$ such that $P(x)$ is true, again, a contradiction!
    have : ∃ (x : X), P x,  
        existsi x, assumption,
    contradiction,
end

/- Theorem
$¬ (∀ x ∈ X, ¬ P(x)) ⇔ ∃ x ∈ X, P(x)$.
-/
theorem neg_all_is_exist (X : Type) (P : X → Prop) : ¬ (∀ x : X, ¬ P x) ↔ ∃ x : X, P x :=
begin
    -- Now that we have gone through quite a lot of LEAN proofs, try to understand this one yourself!
    split,
        {intro h,
        apply classical.by_contradiction,
        push_neg, contradiction
        },
        {rintro ⟨x, hx⟩ h,
        from (h x) hx
        }
end

end M40001
