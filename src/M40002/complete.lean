-- begin header

import M40002.countability

namespace completeness

variables {X Y : Type}
-- end header

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
        {have : b ≤ a := (hc b hb).left,
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
    have hd : s - 1 < s := by linarith,
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

-- Defining the Completeness axiom
axiom completeness (S : set ℝ) (h : bounded_above S) (h1 : S ≠ ∅) : ∃ s : ℝ, sup S s

lemma neg_bdd_above_of_bdd_below {S : set ℝ} 
(h : bounded_below S) : bounded_above {t | -t ∈ S} :=
begin
-- Since S is bounded below let b be its lower.
  cases h with b hb,
-- I now claim that -b is a lower bound of {t | -t ∈ S}.
  refine ⟨-b, λ s hs, _⟩,
-- Let -s ∈ S. But then from b being an lower bound of S, b ≤ -s → s ≤ -b as required!
  linarith [hb (-s) hs]
end

open set

-- Exercise 2.29
theorem completeness_below (S : set ℝ) (h : bounded_below S) (h1 : S ≠ ∅) : ∃ s : ℝ, inf S s :=
begin
-- As we have S is not an empty set, there exists s ∈ S.
  cases ne_empty_iff_nonempty.1 h1 with s hs, 
-- Now let's consider the set T := {t : ℝ | -t ∈ S}.
-- This set is bounded above by our previous lemma so by completeness, it has a supremum (lets call it b).
  cases completeness {t : ℝ | -t ∈ S} 
    (neg_bdd_above_of_bdd_below h) 
    (ne_empty_iff_nonempty.2 ⟨-s, by simp [hs]⟩) with b hb,
-- I claim that -b is the infimum of S.
  refine ⟨-b, _⟩, 
-- As we have previously proven that if s is the supremum of S then -s is the infimum of {t : ℝ | -t ∈ S},
-- it suffices to show that S = {t : ℝ | -t ∈ {t : ℝ | -t ∈ S}}. But this is trivial, so we are done!
  convert neg_set_inf {t : ℝ | -t ∈ S} _ _,
  simp, exact hb
end

open classical

-- Mentimeter Q 9
theorem equality_def (a x : ℝ) : (∀ ε : ℝ, 0 < ε → abs (x - a) < ε) ↔ x = a :=
begin
-- Since this is an if and only if question we need to prove both directions of the equation.
  split,
-- Let use prove the forward direction first. 
-- Suppose otherwise. Then x ≠ a.
    intro h, by_contra h1,
-- It suffices to prove abs (x - a) <  abs (x - a) since that's obviously false.
    suffices : abs (x - a) <  abs (x - a), linarith,
-- So, by choosing ε = abs (x - a), the contradiction follows easily.
    refine h _ (abs_pos_iff.2 $ λ h2, _), 
    rw sub_eq_zero at h2, contradiction,
-- For the other direction it is much easier. 
-- If x = a then abs (x - a) = 0 < ε by construction so we are done!
    intro h, rw h, simp
end

end completeness
