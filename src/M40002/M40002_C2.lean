-- begin header
import data.real.basic
import M40001.M40001_4

namespace M40002

variables {X Y : Type}
-- end header

/- Section
Chapter 2. Numbers
-/

/-
Note: This section deviates from the lecture notes as it is under construction. 
-/

/- Sub-section
Countability
-/

/-
We will be proving the Well-Ordered Principle (A non-empty set of natural numbers has a least element) as it will be usful for proving theorems regarding countability.
-/

lemma no_nat_lt_zero : ¬ (∃ x : ℕ, x < 0) := by {simp}

lemma nat_le_imp_lt_succ (k : ℕ) : ∀ (x : ℕ), x ≤ k ↔ x < k + 1 := by {intro, rwa nat.lt_succ_iff}

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
        rcases this with ⟨y, ⟨hd, he⟩⟩,
        have : ∃ y : ℕ, y < 0 := by {use y, assumption},
        from no_nat_lt_zero this
        },
-- Now assume $k ∈ B$ for some $k ∈ ℕ$, then we need to prove $k + 1 ∈ B$, i.e. we need to prove $∀ x ∈ ℕ, x ≤ k + 1 → x ∉ S$.
        {rw set.mem_set_of_eq at hk,
        rw set.mem_set_of_eq, 
-- Let $x$ be an arbitary natural number thats less than $k + 1$. Suppose $x ∈ S$, we will show a contradiction.
        intros x hx hb,
-- As $x ≤ k ⇔ x < k + 1$, we have $x < k + 1 → x ∉ S$.
        have hl : x < k + 1 → x ∉ S := by {rwa ←nat_le_imp_lt_succ, from hk x},
-- Then as we have assumed $x ∈ S$, $x ≥ k + 1$ since $x < k + 1 → x ∉ S$.
        have : x = k + 1 := 
            by {cases lt_trichotomy x (k + 1),
                {exfalso, from (hl h_1) hb},
                {cases h_1,
                    {assumption},
-- But we have $x < k + 1$, thus, by the trichotomy axiom, $x = k + 1$.
                    {have : k + 1 < x ∧ x ≤ nat.succ k := ⟨h_1, hx⟩, 
                    revert this, simp
                    }
                }
            },
-- Then, as $S$ has no least element, there is some $s ∈ S, s < k + 1$.
        rw this at hb,
        have hc : ∃ (s : ℕ), s ∈ S ∧ s < k + 1 := by {apply ha, assumption},
        rcases hc with ⟨y, ⟨hd, he⟩⟩,
-- But as $k ∈ B$, $s < k + 1 ⇒ s ∉ S$, we have a contradiction! Therefore, by mathematical induction, we have $B = ℕ$
        apply hk y,
        rwa nat_le_imp_lt_succ, assumption
        }
        },
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
def countable (A : set(X)) := ∃ f : ℕ → A, function.bijective f

/-
Intuitively, we can think of this as putting the elements of $S$ into a list with no repeates.
-/

lemma inverse_refl (f : X → Y) (g : Y → X): M40001.two_sided_inverse f g ↔ M40001.two_sided_inverse g f :=
by {split,
    all_goals {rintro ⟨ha, hb⟩, from ⟨hb, ha⟩},   
}

/- Theorem
 Given a set $A$, if there exists a function $f : A → ℕ$ where $f$ is bijective then $A$ is countable. 
-/
theorem countable_rev : ∀ (S : set X), countable S ↔ (∃ g : S → ℕ, function.bijective g) :=
begin
    intro S,
    split,
        all_goals{rintro ⟨f, hf⟩},
        {suffices : ∃ (g : S → ℕ), M40001.two_sided_inverse f g, 
            by {cases this with g hg, use g, rw ←M40001.exist_two_sided_inverse, use f, rwa inverse_refl},
        rwa M40001.exist_two_sided_inverse,
        },

        {have : ∃ (g : ℕ → S), M40001.two_sided_inverse f g,
            by {rwa M40001.exist_two_sided_inverse},
        cases this with g hg,
        use g,
        rwa ←M40001.exist_two_sided_inverse, 
        use f, rwa inverse_refl
        }
end

/- Sub-section
The Completeness Axiom
-/

/- Theorem
If a set $S ⊂ ℝ$ has maximums $a$ and $b$, then $a = b$, i.e. the maximum of a set is unique.
-/
theorem unique_max (S : set ℝ) : ∀ a b ∈ S, (∀ x ∈ S, x ≤ a ∧ x ≤ b) → a = b :=
begin
    intros a b ha hb hc,
    have : a ≤ b := (hc a ha).right,
    cases lt_or_eq_of_le this,
        {clear this,
        have : b ≤ a := (hc b hb).left,
        rw ←not_lt at this,
        contradiction
        },
        {assumption}
end

/- Theorem
If a set $S ⊂ ℝ$ has minimums $a$ and $b$, then $a = b$, i.e. the minimum of a set is unique.
-/
theorem neg_set_min (S : set ℝ) (s : ℝ) (h0 : s ∈ S) (h1 : ∀ x ∈ S, x ≤ s): 
    ∀ x ∈ {t : ℝ | -t ∈ S}, -s ≤ x ∧ -s ∈ {t : ℝ | -t ∈ S} :=
begin
    intros x hx,
    split,
    {rwa neg_le,
    rw set.mem_set_of_eq at hx,
    apply h1, assumption
    },
    {rwa set.mem_set_of_eq,
    simpa
    }
end

/- Definition
A set $S ⊂ ℝ$ is bounded above if and only if $∃ M ∈ ℝ, ∀ s ∈ S, s ≤ M$
-/
def bounded_above (S : set ℝ) := ∃ M : ℝ, ∀ s ∈ S, s ≤ M

/- Definition
We call $M$ a upper bound of $S ⊂ ℝ$ if and only if $∀ s ∈ S, s ≤ M$.
-/
def upper_bound (S : set ℝ) (M : ℝ) := ∀ s ∈ S, s ≤ M

/-
We can deduce some properties straight away from these definitions.
-/

/- Corollary
A set $S ⊂ ℝ$ is bounded above if and only if there exists a $M ∈ ℝ$, $M$ is an upper bound of $S$
-/
theorem bdd_above_iff_have_upr_bd (S : set ℝ) : (∃ M : ℝ, upper_bound S M) ↔ bounded_above S :=
by {split, all_goals {rintro ⟨M, hM⟩, use M, assumption} }

/- Corollary
If $S$ has an upperbound $M$, then $∀ x ∈ R, x ≥ M$ implies $x$ is a upper bound of $S$ 
-/
theorem bigger_upperbound (S : set ℝ) (s : ℝ) (h : upper_bound S s) :
    ∀ x : ℝ, s ≤ x → upper_bound S x :=
by {intros x hx y hy, from le_trans (h y hy) hx}

/-
We will define lower bounds and bounded below in a similar fashion.
-/

/- Definition
A set $S ⊂ ℝ$ is bounded below if and only if $∃ M ∈ ℝ, ∀ s ∈ S, s ≥ M$
-/
def bounded_below (S : set ℝ) := ∃ M : ℝ, ∀ s ∈ S, M ≤ s

/- Definition
We call $M$ a lower bound of $S ⊂ ℝ$ if and only if $∀ s ∈ S, s ≥ M$.
-/
def lower_bound (S : set ℝ) (M : ℝ) := ∀ s ∈ S, M ≤ s

/- Corollary
A set $S ⊂ ℝ$ is bounded below if and only if there exists a $M ∈ ℝ$, $M$ is an lower bound of $S$
-/
theorem bdd_below_iff_have_lwr_bd (S : set ℝ) : (∃ M : ℝ, lower_bound S M) ↔ bounded_below S :=
by {split, all_goals {rintro ⟨M, hM⟩, use M, assumption} }

/- Exercise
If $s ∈ ℝ$ is an upper bound of a set $S ⊂ ℝ$, then $-s$ is a lower bound of the set ${t ∈ ℝ | -t ∈ S}$.
-/
theorem upr_bd_neg_set_lwr_bd (S : set ℝ) (s : ℝ) : upper_bound S s ↔ lower_bound {t : ℝ | -t ∈ S} (-s) :=
begin
    split,
        all_goals {intros h x hx},
        {rw set.mem_set_of_eq at hx,
        suffices : (-x) ≤ s, rwa neg_le,
        from h (-x) hx
        },
        unfold lower_bound at h,
        suffices : (-s) ≤ (-x), simp at this, assumption,
        have : (-x) ∈ {t : ℝ | -t ∈ S} := by {rwa set.mem_set_of_eq, simp, assumption},
        from h (-x) this
end

/- Definition
We call a set $S ⊂ ℝ$ bounded if it is bounded above and below.
-/
def bounded (S : set ℝ) := bounded_above S ∧ bounded_below S

-- Okay, so I've switched around the definition of supremums but dw, the two definitions are equiv.
def sup (S : set ℝ) (x : ℝ) := upper_bound S x ∧ (∀ y : ℝ, y < x → ¬ (upper_bound S y)) -- Check out sup_def for the definition from the lecture notes
def inf (S : set ℝ) (x : ℝ) := lower_bound S x ∧ (∀ y : ℝ, x < y → ¬ (lower_bound S y))

-- Exercise 2.24
theorem unique_sup (S : set ℝ) : ∀ a b ∈ S, sup S a ∧ sup S b → a = b :=
begin
    rintros a b ha hb ⟨⟨bda, supa⟩, ⟨bdb,supb⟩⟩,
    have hc : ∀ s ∈ S, s ≤ a ∧ s ≤ b := by {intros s hs, from ⟨bda s hs, bdb s hs⟩},
    from unique_max S a b ha hb hc
end

theorem sup_non_empty (S : set ℝ) (s : ℝ) (h : sup S s) : S ≠ ∅ :=
begin
    cases h with ha hb,
    intro, 
    have hc : upper_bound S (s - 1) := 
        by {intros x hx,
        rw a at hx,
        simp at hx, contradiction
        },
    have hd : s - 1 < s := by {simp, by norm_cast},
    replace hb : ¬ upper_bound S (s - 1) := by {apply hb (s - 1) hd},
    contradiction
end

theorem neg_set_inf (S : set ℝ) (s : ℝ) (h : sup S s) : 
    inf {t : ℝ | -t ∈ S} (-s) :=
begin
    cases h with hbd hlub,
    split,
        {intros x hx,
        apply classical.by_contradiction,
        intro h, push_neg at h,
        have : -s ≤ x := by {rw neg_le, from (hbd (-x) hx)},
        apply not_le_of_lt h, assumption
        },
        {intros y hy hlbd,
        have : upper_bound S (-y) := 
            by {intros x hx,
            apply classical.by_contradiction,
            intro h, push_neg at h,
            unfold lower_bound at hlbd,
            have : y ≤ -x := 
                by {replace hx : -x ∈ {t : ℝ | -t ∈ S},
                    rw set.mem_set_of_eq, simp, assumption,
                from hlbd (-x) hx
                },
            apply not_le_of_lt h, rwa le_neg
            },
        replace hy : -y < s := by {rwa neg_lt},
        from hlub (-y) hy this
        }
end

theorem sup_def (S : set ℝ) (s : ℝ) : sup S s ↔ upper_bound S s ∧ ∀ x : ℝ, (upper_bound S x → s ≤ x) :=
begin
    split,
        {rintros ⟨ha, hb⟩,
        split,
            {intros x hx,
            from ha x hx
            },
            {intros x hx,
            suffices : ¬ x < s, revert this, simp,
            intro, apply hb x, repeat {assumption}}
        },
        {rintros ⟨ha, hb⟩, split,
            {assumption},
            {intros x hx hc,
            replace hx : ¬ s ≤ x := by {push_neg, assumption},
            from hx (hb x hc)
            }
        }
end

theorem inf_def (S : set ℝ) (s : ℝ) : inf S s ↔ lower_bound S s ∧ ∀ x : ℝ, (lower_bound S x → x ≤ s) :=
begin -- proof essentially identical to that of sup_def
        split,
        {rintros ⟨ha, hb⟩,
        split,
            {intros x hx,
            from ha x hx
            },
            {intros x hx,
            suffices : ¬ s < x, revert this, simp,
            intro, apply hb x, repeat {assumption}}
        },
        {rintros ⟨ha, hb⟩, split,
            {assumption},
            {intros x hx hc,
            replace hx : ¬ x ≤ s := by {push_neg, assumption},
            from hx (hb x hc)
            }
        }
end

theorem completeness (S : set ℝ) (h : bounded_above S) (h1 : S ≠ ∅) : ∃ s : ℝ, sup S s :=
begin
    sorry
end

-- Exercise 2.29
theorem completeness_below (S : set ℝ) (h : bounded_below S) (h1 : S ≠ ∅) : ∃ s : ℝ, inf S s :=
begin
    let T := {t : ℝ | -t ∈ S},
    rw ←bdd_below_iff_have_lwr_bd at h,
    cases h with M hM,
    have hα : upper_bound T (-M) :=
        by {rwa upr_bd_neg_set_lwr_bd,
        simp, assumption
        },
    have hβ : bounded_above T := by {rw ←bdd_above_iff_have_upr_bd, use (-M), assumption},
    have hγ : T ≠ ∅,
        by {cases (set.exists_mem_of_ne_empty h1), 
        rw set.ne_empty_iff_exists_mem,
        use (-w), rwa set.mem_set_of_eq, simp, assumption
        },
    have hε : ∃ k : ℝ, sup T k := completeness T hβ hγ,
    cases hε with k hk,
    use (-k),
    suffices : S = {t : ℝ | -t ∈ T},
        rw this,
        from neg_set_inf T k hk,
    ext, split,
        all_goals {repeat {rw set.mem_set_of_eq}, simp}
end

theorem sqrt_three_in_R : ∃ x : ℝ, x ^ 2 = 3 :=
begin
    sorry
end

-- Triangle inequalities

theorem triangle_inequality : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b :=
begin
    intros a b,
    from abs_add a b -- Maybe do this myself?
end

-- The other triangle inequalities too?

-- Mentimeter Q 9
theorem equality_def (a x : ℝ) : (∀ ε : ℝ, 0 < ε → abs (x - a) < ε) ↔ x = a :=
begin
    split,
        {intro h,
        apply classical.by_contradiction,
        intro ha,
        have : x - a ≠ 0 := 
            by {revert ha,
            from sub_ne_zero.mpr
            },
        have hb : abs (x - a) < abs (x - a) := 
            by {from h (abs (x - a)) (abs_pos_iff.mpr this)},
        revert hb, finish
        },
        {intro h,
        have : x - a = 0 :=
            by {revert h, 
            from sub_eq_zero.mpr
            },
        rwa this,
        simp
        }
end


end M40002