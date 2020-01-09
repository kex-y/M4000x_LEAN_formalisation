-- M40002 (Analysis I) Chapter 4. Series

import M40002.M40002_C3

namespace M40002

-- Definition of convergent sums
def partial_sum_to (a : ℕ → ℝ) (n : ℕ) := finset.sum (finset.range n) a
notation `∑` a := partial_sum_to a

def sum_converges_to (a : ℕ → ℝ) (l : ℝ) := (partial_sum_to a) ⇒ l
notation a ` ∑⇒ ` l := sum_converges_to a l

def sum_convergent (a : ℕ → ℝ) := ∃ l : ℝ, a ∑⇒ l
notation ` ∑⇒ ` a := sum_convergent a

-- s n - s (n - 1) = a n
lemma successive_diff {a : ℕ → ℝ} {n : ℕ} : (partial_sum_to a (n + 1)) - (partial_sum_to a n) = a n :=
by {unfold partial_sum_to,
    rw finset.sum_range_succ,
    simp
}

-- ∑ a is convergent implies a → 0
theorem trivial_test (a : ℕ → ℝ) : (∑⇒ a) → a ⇒ 0 :=
begin
    intros h ε hε,
    cases h with l hl,
    have : cauchy (partial_sum_to a) :=
        by {rwa cauchy_iff_conv,
        use l, from hl
        },
    cases this ε hε with N hN,
    use N, intros n hn,
    rw sub_zero (a n),
    suffices hα : abs (partial_sum_to a n - partial_sum_to a (n + 1)) < ε,
        {rwa [abs_sub, successive_diff] at hα},
    apply hN n (n + 1),
    have : N ≤ n + 1 := by {linarith},
    from ⟨hn, this⟩
end

lemma succ_sum_def {a : ℕ → ℝ} : ∀ k : ℕ, (∑ a) (nat.succ k) = (∑ a) k + a k := 
by {intro k, unfold partial_sum_to,
    rw finset.sum_range_succ,
    from add_comm (a k) (finset.sum (finset.range k) a)
}

-- If a ≥ 0, then ↑ (∑ a)
lemma sum_mono_increasing {a : ℕ → ℝ} (h : ∀ n : ℕ, 0 ≤ a n) : (∑ a) ↑ :=
begin
    intro n, rw succ_sum_def n,
    have hβ : 0 ≤ a n := h n,
    linarith
end

-- If a ≥ 0, then ∑ a is convergent if ∑ a is bounded above
theorem sum_bdd_abv_conv {a : ℕ → ℝ} (h : ∀ n : ℕ, 0 ≤ a n) : (seq_bounded_above (∑ a)) → (∑⇒ a) :=
begin
    intro hα,
    apply mono_increasing_means_conv (∑ a) _,
    split, 
    {from hα},
    {use 0, intro m,
    induction m with k hk,
        {unfold partial_sum_to, simp},
            {rw succ_sum_def k,
            from add_nonneg hk (h k)
            },
        },
    from sum_mono_increasing h
end

-- Comparison Test. If 0 ≤ a ≤ b, and if ∑ b converges then so do ∑ a
theorem comparison_test {a b : ℕ → ℝ} : (∀ n : ℕ, 0 ≤ a n ∧ a n ≤ b n) ∧ (∑⇒ b) → ∑⇒ a := 
begin
    rintro ⟨hα, ⟨l, hl⟩⟩,
    apply sum_bdd_abv_conv,
        {intro n,
        from (hα n).left
        },
        {rcases converge_is_bdd (∑ b) ⟨l, hl⟩ with ⟨⟨N, hN⟩, blw⟩,
        use N, intro n,
        have : (∑ a) n ≤ (∑ b) n :=
            by {induction n with k hk,
            unfold partial_sum_to, simp,
            repeat {rw succ_sum_def},
            have : a k ≤ b k := (hα k).right,
            linarith
            },
        from le_trans this (hN n)
        }
end


end M40002