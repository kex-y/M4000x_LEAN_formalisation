-- M40002 (Analysis I) Chapter 4. Series

import M40002.M40002_C3

namespace M40002

-- Definition of convergent sums
def partial_sum_to (a : ℕ → ℝ) (n : ℕ) := finset.sum (finset.range n) a

def sum_converges_to (a : ℕ → ℝ) (l : ℝ) := (partial_sum_to a) ⇒ l
notation a ` ∑⇒ ` l := sum_converges_to a l

def sum_convergent (a : ℕ → ℝ) := ∃ l : ℝ, a ∑⇒ l
notation ` ∑⇒ ` a := sum_convergent a

#check finset.sum_range_succ
-- s n - s (n - 1) = a n
lemma successive_diff (a : ℕ → ℝ) (n : ℕ) : (partial_sum_to a (n + 1)) - (partial_sum_to a n) = a (n + 1) :=
by {unfold partial_sum_to,
    sorry

}

-- ∑ a is convergent implies a → 0
theorem trivial_test (a : ℕ → ℝ) : (∑⇒ a) → a ⇒ 0 :=
begin
    intros h ε hε,
    cases h with l hl,
    sorry


end




end M40002