-- M40002 (Analysis I) Chapter 6. Differentiation

import M40002.M40002_C5

namespace M40002

-- Definition of a function being differntiable at a point
def differentiable_at (f : ℝ → ℝ) (a : ℝ) := ∃ l : ℝ, func_converges_to (λ x : ℝ, (f x - f a) / (x - a)) a l
def differentiable (f : ℝ → ℝ) := ∀ a : ℝ, differentiable_at f a

end M40002