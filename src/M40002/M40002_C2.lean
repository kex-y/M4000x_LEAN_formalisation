-- M40002 (Analysis I) Chapter 2. Numbers

import data.real.basic
import data.rat.basic
import tactic.ring
import M40001.M40001_4

namespace M40002


variables {X Y : Type}

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
theorem nat_sub_countable : ∀ (S : set ℕ), (∀ n : ℕ, ∃ s ∈ S, s > n) → countable S :=
begin
    intros S h,
    unfold countable,
    sorry
end

end M40002