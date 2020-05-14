-- begin header

import M40001.M40001_C2

namespace numbers

variables {X Y : Type}
-- end header

/- Section
Chapter 2. Numbers
-/

/- Sub-section
Countability
-/

/-
We will be proving the Well-Ordered Principle (A non-empty set of natural numbers 
has a least element) as it will be usful for proving theorems regarding countability.

In LEAN's maths library, there is a useful lemma that does the samething. 
See nat.find
-/

open function M40001

/- Theorem
The Well-Ordered Principle. If $S$ is a set of natural numbers and is non-empty, then there exists an element $n ∈ S, ∀s ∈ S, n ≤ s$.
-/
theorem well_ordered_principle (S : set ℕ) (h : S ≠ ∅) : ∃ n ∈ S, ∀ s ∈ S, n ≤ s :=
begin
-- We'll prove the Well-Ordered Principle by contradiction. Suppose there exist $∅ ≠ S ⊂ ℕ$, $S$ does not have a least element.
    apply classical.by_contradiction, push_neg, intro ha,
-- Then let us create the set $B := {n ∈ ℕ | ∀ x ≤ n, x ∉ S}$. (Notice that all elements of $S$ are bigger that all elements of $B$.)
    let B := {n : ℕ | ∀ x ≤ n, x ∉ S},
-- I claim that $B = ℕ$.
    have : ∀ x : ℕ, x ∈ B,
-- We will prove this by doing an induction on $x$.
        by {intro x, induction x with k hk,
-- We first need to prove that $0 ∈ B$. As we have $∀ s ∈ S, s ∈ ℕ ⇒ s ≥ 0$, it suffices to prove that $0 ∉ S$.
        {rw set.mem_set_of_eq,
        intros x hb hc,
        replace hb : x = 0 :=
            by {revert hb, simp},
        rw hb at hc,
-- But if $0 ∈ S$ then $S$ has a minimum, $0$ can't be in $S$, implying $0 ∈ B$.
        have : ∃ (s : ℕ), s ∈ S ∧ s < 0 := by {apply ha 0, assumption},
        rcases this with ⟨y, ⟨_, he⟩⟩,
        refine not_lt_of_ge _ he, norm_num,
        },
-- Now assume $k ∈ B$ for some $k ∈ ℕ$, then we need to prove $k + 1 ∈ B$, i.e. we need to prove $∀ x ∈ ℕ, x ≤ k + 1 → x ∉ S$.
        {rw set.mem_set_of_eq at hk,
        rw set.mem_set_of_eq, 
-- Let $x$ be an arbitary natural number thats less than $k + 1$. Suppose $x ∈ S$, we will show a contradiction.
        intros x hx hb,
-- As $x ≤ k ⇔ x < k + 1$, we have $x < k + 1 → x ∉ S$.
        have hl : x < k + 1 → x ∉ S := by {rwa nat.lt_succ_iff, from hk x},
-- Then as we have assumed $x ∈ S$, $x ≥ k + 1$ since $x < k + 1 → x ∉ S$.
        have : x = k + 1 := 
            by {cases lt_trichotomy x (k + 1),
                {exfalso, from (hl h_1) hb},
                {cases h_1,
                    {assumption},
-- But we have $x < k + 1$, thus, by the trichotomy axiom, $x = k + 1$.
                    {have : k + 1 < x ∧ x ≤ nat.succ k := ⟨h_1, hx⟩, 
                    revert this, simp
                    } } },
-- Then, as $S$ has no least element, there is some $s ∈ S, s < k + 1$.
        rw this at hb,
        have hc : ∃ (s : ℕ), s ∈ S ∧ s < k + 1 := by {apply ha, assumption},
        rcases hc with ⟨y, ⟨hd, he⟩⟩,
-- But as $k ∈ B$, $s < k + 1 ⇒ s ∉ S$, we have a contradiction! Therefore, by mathematical induction, we have $B = ℕ$
        apply hk y,
        rwa ←nat.lt_succ_iff, assumption
        } },
-- As, by construction, we have $S$ and $B$ are disjoint. Thus, since $S ⊆ ℕ, B = ℕ ⇒ S = ∅$.
    apply h,
    have hSempty : ∀ n ∈ B, n ∉ S := 
        by {intros n hn hs,
        rw set.mem_set_of_eq at hn,
        apply hn n, refl, assumption
        },
    ext, split,
    all_goals {intro he},
    {from hSempty x (this x) he},
-- But $S = ∅$ is a contradiction as we assumed its non-empty. Thus such an $S$ does not exist!
    {simp at he, contradiction}
end

/- Definition
A set $S$ is countable if and only if there exists a bijection $f : ℕ → S$.
-/
def countable (A : set(X)) := ∃ f : ℕ → A, bijective f

/-
Intuitively, we can think of this as putting the elements of $S$ into a list with no repeates.
-/

lemma inverse_refl (f : X → Y) (g : Y → X): two_sided_inverse f g ↔ two_sided_inverse g f :=
by {split,
    all_goals {rintro ⟨ha, hb⟩, from ⟨hb, ha⟩},   
}

/- Theorem
 Given a set $A$, if there exists a function $f : A → ℕ$ where $f$ is bijective then $A$ is countable. 
-/
theorem countable_rev : ∀ (S : set X), countable S ↔ (∃ g : S → ℕ, bijective g) :=
begin
    intro S,
    split,
        all_goals{rintro ⟨f, hf⟩},
        {suffices : ∃ (g : S → ℕ), two_sided_inverse f g, 
            by {cases this with g hg, use g, 
            rw ←exist_two_sided_inverse, use f, rwa inverse_refl},
        rwa exist_two_sided_inverse,
        },

        {have : ∃ (g : ℕ → S), two_sided_inverse f g,
            by {rwa exist_two_sided_inverse},
        cases this with g hg,
        use g,
        rwa ←exist_two_sided_inverse, 
        use f, rwa inverse_refl
        }
end

end numbers