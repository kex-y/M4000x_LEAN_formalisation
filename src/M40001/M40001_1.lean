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

universe u
variable {Ω : Type*}

-- Let $Ω$ be a fixed set with subsets $X$ and $Y$, then

/- Theorem
(1) $\bar{X ∪ Y} = \bar{X} ∩ \bar{Y},
-/
theorem de_morg_set_a (X Y : set Ω) : - (X ∪ Y) = - X ∩ - Y :=
by {rwa set.compl_union}
/- Theorem
(2) $\bar{X ∩ Y} = \bar{X} ∪ \bar{Y}.
-/
theorem de_morg_set_b (X Y : set Ω) : - (X ∩ Y) = - X ∪ - Y :=
by {rwa set.compl_inter}

theorem de_morg_set_a_temp (X Y : set Ω) : - (X ∪ Y) = (- X) ∩ (- Y) :=
begin -- How would one actually prove this without rw?
    ext, split,
    {intro h,
    rw set.compl_union at h,
    assumption
    },
    {intro h,
    rw set.compl_union,
    assumption
    }
end

/- Section
1.7.1 "For All" and "There Exists"
-/

/- Theorem
Given a propositon $P$ whose truth value is dependent on $x ∈ X$, then $∀ x ∈ X, ¬ P(x) ⇔ ¬ (∃ x ∈ X, P(x))$, and
-/
theorem neg_exist_is_all (X : Type) (P : X → Prop) : (∀ x : X, ¬ P x) ↔ ¬ (∃ x : X, P x) :=
begin
    split,
    {rintro h ⟨x, hx⟩,
    from (h x) hx
    },
    {intros ha x hx,
    have : ∃ (x : X), P x,  
        existsi x, assumption,
    contradiction,
    }
end
/- Theorem
$¬ (∀ x ∈ X, ¬ P(x)) ⇔ ∃ x ∈ X, P(x)$.
-/
theorem neg_all_is_exist (X : Type) (P : X → Prop) : ¬ (∀ x : X, ¬ P x) ↔ ∃ x : X, P x :=
begin -- is there a way to do this without push_neg?
    split,
    {intro h,
    apply classical.by_contradiction,
    push_neg, contradiction
    },
    {rintro ⟨x, hx⟩ h,
    from (h x) hx
    }
end








































end M40001_1