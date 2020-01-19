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

-- Algebra of limits for sums
lemma sum_add_sum_split {a b : ℕ → ℝ} : (∑ a) + (∑ b) = (∑ a + b) :=
begin
    rw [seq_add_seq, function.funext_iff], 
    intro n,
    unfold partial_sum_to,
    induction n with k hk,
        {simp},
        {repeat {rw finset.sum_range_succ},
        rw [←hk, seq_add_seq], simp
        }
end

theorem add_sum_lim_conv {a b : ℕ → ℝ} {l m : ℝ} (h₁ : a ∑⇒ l) (h₂ : b ∑⇒ m) : (a + b) ∑⇒ (l + m) :=
begin
    unfold sum_converges_to,
    rw ←sum_add_sum_split,
    apply add_lim_conv,
    from ⟨h₁, h₂⟩
end

lemma scalar_mul_sum_split {a : ℕ → ℝ} {m : ℝ} : ((∑ a) × m) = ∑ (a × m) :=
begin
    rw function.funext_iff,
    intro n, rw seq_mul_real,
    unfold partial_sum_to,
    induction n with k hk,
        {simp},
        {rw [finset.sum_range_succ, add_mul, hk],
        have : a k * m = (a × m) k := rfl,
        rwa [this, ←finset.sum_range_succ]
        }
end

theorem scalar_sum_lim_conv {a : ℕ → ℝ} {l m : ℝ} (h₁ : a ∑⇒ l) : (a × m) ∑⇒ l * m :=
begin
    unfold sum_converges_to,
    rw ←scalar_mul_sum_split,
    apply mul_lim_conv, 
    from h₁,
    from cons_conv
end

-- Defining absolute convergence
noncomputable def abs_seq (a : ℕ → ℝ) (n : ℕ) := abs (a n)
def abs_sum_converge (a : ℕ → ℝ) := ∑⇒ abs_seq a

-- Absolutely convergen implies normal convergence
lemma sum_diff {a : ℕ → ℝ} {n m : ℕ} (h₁ : n < m) : (∑ a) m - (∑ a) n = finset.sum (finset.Ico n m) a :=
begin
    unfold partial_sum_to, 
    induction m with k hk,
        {exfalso, from nat.not_succ_le_zero n h₁},
        {rw [finset.sum_range_succ, finset.sum_Ico_succ_top],
        swap, from nat.lt_succ_iff.mp h₁,
        simp,
        cases nat.lt_succ_iff_lt_or_eq.mp h₁,
            {rw [←sub_eq_add_neg, hk h]},
            {rw h, simp}
        }
end

lemma sum_le (a b : ℕ → ℝ) {n m : ℕ} (h₁ : ∀ n : ℕ, a n ≤ b n) : finset.sum (finset.Ico n m) a ≤ finset.sum (finset.Ico n m) b :=
begin
    induction m with k hk,
        {rw finset.Ico.eq_empty_iff.mpr (zero_le n), simp},
        {cases le_or_lt n k,
            {repeat {rw finset.sum_Ico_succ_top h},
            apply add_le_add hk _,
            from h₁ k
            },
            {rw finset.Ico.eq_empty_iff.mpr (nat.succ_le_iff.mpr h),
            simp
            }
        }
end

lemma sum_pos {a : ℕ → ℝ} {n m : ℕ} (h₁ : ∀ k : ℕ, 0 ≤ a k) : 0 ≤ finset.sum (finset.Ico n m) a :=
begin
    induction m with k hk,
        {rw finset.Ico.eq_empty_iff.mpr (zero_le n), simp},
        {cases le_or_lt n k,
            {rw finset.sum_Ico_succ_top h,
            from add_nonneg hk (h₁ k)
            },
            {rw finset.Ico.eq_empty_iff.mpr (nat.succ_le_iff.mpr h),
            simp
            }
        }
end

lemma neg_sum {a : ℕ → ℝ} {n m : ℕ} : - finset.sum (finset.Ico n m) a = finset.sum (finset.Ico n m) (a × -1) :=
begin
    induction m with k hk,
        {rw finset.Ico.eq_empty_iff.mpr (zero_le n), simp},
        {cases le_or_lt n k,
            {repeat {rw finset.sum_Ico_succ_top h},
            unfold seq_mul_real, simp
            },
            {rw finset.Ico.eq_empty_iff.mpr (nat.succ_le_iff.mpr h),
            simp
            }
        }
end

theorem abs_conv_to_conv {a : ℕ → ℝ} : abs_sum_converge a → ∑⇒ a :=
begin
    intro h₁,
    suffices : cauchy (∑ a),
        cases cauchy_iff_conv.mp this with l hl,
        use l, from hl,
    have hcauchy : cauchy (∑ abs_seq a) := cauchy_iff_conv.mpr h₁,
    unfold cauchy at hcauchy,
    intros ε hε,
    cases hcauchy ε hε with N hN,
    use N, intros n m h₂,
    replace hN : abs ((∑abs_seq a) n - (∑abs_seq a) m) < ε := hN n m h₂,
    cases lt_trichotomy n m,
        swap, cases h,
        {rw h, simp, from hε},
        {rw sum_diff h,
        rw sum_diff h at hN,
        apply lt_of_le_of_lt _ hN,
        rw abs_le,
        split, swap,
            {have : ∀ k : ℕ, a k ≤ abs_seq a k := λ k : ℕ,
                by {from le_max_left (a k) (- a k)},
            apply le_trans (sum_le a (abs_seq a) this),
            from le_max_left (finset.sum (finset.Ico m n) (abs_seq a)) (-finset.sum (finset.Ico m n) (abs_seq a))
            },
            {rw abs_of_nonneg, swap, 
                {apply sum_pos,
                intro k, from abs_nonneg (a k)},
                {rw neg_sum, apply sum_le,
                intro n, unfold seq_mul_real,
                simp, rw neg_le, from le_max_right (a n) (-a n)
                }
            }
        },
        {rw [abs_sub, sum_diff h],
        rw [abs_sub, sum_diff h] at hN,
        apply lt_of_le_of_lt _ hN,
        rw abs_le,
        split, swap,
            {have : ∀ k : ℕ, a k ≤ abs_seq a k := λ k : ℕ,
                by {from le_max_left (a k) (- a k)},
            apply le_trans (sum_le a (abs_seq a) this),
            from le_max_left (finset.sum (finset.Ico n m) (abs_seq a)) (-finset.sum (finset.Ico n m) (abs_seq a))
            },
            {rw abs_of_nonneg, swap, 
                {apply sum_pos,
                intro k, from abs_nonneg (a k)},
                {rw neg_sum, apply sum_le,
                intro n, unfold seq_mul_real,
                simp, rw neg_le, from le_max_right (a n) (-a n)
                }
            }
        }
end


-- set_option trace.simplify.rewrite true

end M40002