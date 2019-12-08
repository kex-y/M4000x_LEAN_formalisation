-- M40002 (Analysis I) Chapter 2. Numbers

import data.real.basic
import M40001.M40001_4

namespace M40002


variables {X Y : Type}

-- Natural number lemmas for countability

lemma no_nat_lt_zero : ¬ (∃ x : ℕ, x < 0) := by {simp}

lemma nat_le_imp_lt_succ (k : ℕ) : ∀ (x : ℕ), x ≤ k ↔ x < k + 1 := by {intro, rwa nat.lt_succ_iff}

theorem well_ordered_principle (S : set ℕ) (h : S ≠ ∅) : ∃ n ∈ S, ∀ s ∈ S, n ≤ s :=
begin
-- We'll prove this by contradiction
    apply classical.by_contradiction, push_neg, intro ha,
-- The general idea is to show that B = ℕ which implies S = ∅ which is a contradiction
    let B := {n : ℕ | ∀ x ≤ n, x ∉ S},
    have : ∀ x : ℕ, x ∈ B,
-- We will do a induction on x
        by {intro x, induction x with k hk,
-- Base case (0 ∈ B)
        {rw set.mem_set_of_eq,
        intros x hb hc,
        replace hb : x = 0 :=
            by {revert hb, simp},
        rw hb at hc,
        have : ∃ (s : ℕ), s ∈ S ∧ s < 0 := by {apply ha 0, assumption},
        rcases this with ⟨y, ⟨hd, he⟩⟩,
        have : ∃ y : ℕ, y < 0 := by {use y, assumption},
        from no_nat_lt_zero this
        },
-- Inductive step (x ∈ B → x + 1 ∈ B)
        {rw set.mem_set_of_eq at hk,
        rw set.mem_set_of_eq, intros x hx hb,
        have hl : x < k + 1 → x ∉ S := by {rwa ←nat_le_imp_lt_succ, from hk x},
        have : x = k + 1 := 
            by {cases lt_trichotomy x (k + 1),
                {exfalso, from (hl h_1) hb},
                {cases h_1,
                    {assumption},
                    {have : k + 1 < x ∧ x ≤ nat.succ k := ⟨h_1, hx⟩, 
                    revert this, simp
                    }
                }
            },
        rw this at hb,
        have hc : ∃ (s : ℕ), s ∈ S ∧ s < k + 1 := by {apply ha, assumption},
        rcases hc with ⟨y, ⟨hd, he⟩⟩,
        apply hk y,
        rwa nat_le_imp_lt_succ, assumption
        }
        },
-- Okay! Now we just have to show that B = ℕ → A = ∅
    apply h,
    have hSempty : ∀ n ∈ B, n ∉ S := 
        by {intros n hn hs,
        rw set.mem_set_of_eq at hn,
        apply hn n, refl, assumption
        },
    ext, split,
    all_goals {intro he},
    {from hSempty x (this x) he},
    {simp at he, contradiction}
end

-- Countability

def countable (A : set(X)) := ∃ f : ℕ → A, function.bijective f

lemma inverse_refl (f : X → Y) (g : Y → X): M40001.two_sided_inverse f g ↔ M40001.two_sided_inverse g f :=
by {split,
    all_goals {rintro ⟨ha, hb⟩, from ⟨hb, ha⟩},   
}

-- ∃ f : A → ℕ where f is bijective also means A is countable
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

-- All infinite subsets of ℕ are countable

def exist_min (S : set ℕ) := ∃ s ∈ S, ∀ x ∈ S, s ≤ x

theorem nat_sub_countable : ∀ (S : set ℕ), (∀ n : ℕ, ∃ s ∈ S, s > n) → countable S :=
begin
    intros S h,
    unfold countable,
    sorry
end

-- Okay... I've skipped a bunch here cause I don't like countability :(

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

def bounded_above (S : set ℝ) := ∃ M : ℝ, ∀ s ∈ S, s ≤ M
def upper_bound (S : set ℝ) (M : ℝ) := ∀ s ∈ S, s ≤ M

example (p : Prop) : p → p := by {finish}

theorem bdd_above_iff_have_upr_bd (S : set ℝ) : (∃ M : ℝ, upper_bound S M) ↔ bounded_above S :=
begin
    split,
    all_goals {rintro ⟨M, hM⟩, use M, assumption}
end

def bounded_below (S : set ℝ) := ∃ M : ℝ, ∀ s ∈ S, M ≤ s
def lower_bound (S : set ℝ) (M : ℝ) := ∀ s ∈ S, M ≤ s

theorem bdd_below_iff_have_lwr_bd (S : set ℝ) : (∃ M : ℝ, lower_bound S M) ↔ bounded_below S :=
begin
    split,
    all_goals {rintro ⟨M, hM⟩, use M, assumption}
end

def bounded (S : set ℝ) := bounded_above S ∧ bounded_below S

def sup (S : set ℝ) (x : ℝ) := upper_bound S x ∧ (∀ y : ℝ, y < x → ¬ (upper_bound S y))
def inf (S : set ℝ) (x : ℝ) := lower_bound S x ∧ (∀ y : ℝ, x < y → ¬ (lower_bound S y))

theorem unique_sup (S : set ℝ) : ∀ a b ∈ S, sup S a ∧ sup S b → a = b :=
begin
    rintros a b ha hb ⟨⟨bda, supa⟩, ⟨bdb,supb⟩⟩,
    have hc : ∀ s ∈ S, s ≤ a ∧ s ≤ b := by {intros s hs, from ⟨bda s hs, bdb s hs⟩},
    from unique_max S a b ha hb hc
end

theorem completeness (S : set ℝ) (h : bounded_above S) : ∃ s : ℝ, sup S s :=
begin
    sorry
end

end M40002