-- begin header
import tactic.ring
import data.rat.basic
import data.rat.cast
import tactic.linarith
import tactic.norm_cast

namespace M40001_1
-- end header

/- Section
1.7 Sets and Propositions
-/

variable {Ω : Type}

-- Let $Ω$ be a fixed set with subsets $X$ and $Y$, then

/- Theorem
(1) $\bar{X ∪ Y} = \bar{X} ∩ \bar{Y},
-/
theorem de_morg_set (X Y : set Ω) : -(X ∪ Y) = (- X) ∩ (- Y) :=
begin
    ext,
    sorry
end















































end M40001_1