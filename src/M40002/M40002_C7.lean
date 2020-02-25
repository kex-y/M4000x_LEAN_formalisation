-- M40002 (Analysis I) Chapter 7. Darboux Integration

import M40002.M40002_C6

namespace M40002

variables {a₁ a₂ : ℝ}

-- Definition of partitions
structure darboux_partition (n : ℕ) (a b : ℝ) :=
(xₖ : ℕ → ℝ)
(seq_min : xₖ 0 = a)
(seq_max : xₖ n = b)
(increasing : strict_mono xₖ)

#check darboux_partition

--theorem lower_inf_exists {n : ℕ} {a b : ℝ} (f : ℝ → ℝ) (xₖ : darboux_partition n a b) : ∀ i ∈ finset.range n, ∃ l : ℝ, inf {t : ℝ | xₖ i < t ∧ }

end M40002