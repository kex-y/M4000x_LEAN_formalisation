-- M40002 (Analysis I) Chapter 5. Continuity

import M40002.M40002_C4

namespace M40002

-- Definition of limits of functions (f(x) → b as x → a)
def func_converges_to (f : ℝ → ℝ) (a b : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs (x - a) < δ ∧ 0 < abs (x - a) → abs (f x - b) < ε
notation f, a ` ⇒ ` b := func_converges_to f a b

-- Definition of continuity at a point
def func_continuous_at (f : ℝ → ℝ) (a : ℝ) := ∃ b : ℝ, func_converges_to f a (f a)

-- Definition of a continuous function
def func_continuous (f : ℝ → ℝ) := ∀ a : ℝ, func_continuous_at f a

end M40002