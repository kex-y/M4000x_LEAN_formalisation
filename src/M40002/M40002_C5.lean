-- M40002 (Analysis I) Chapter 5. Continuity

import M40002.M40002_C4

namespace M40002

-- Definition of limits of functions (f(x) → b as x → a)
def func_converges_to (f : ℝ → ℝ) (a b : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs (x - a) < δ → abs (f x - b) < ε

-- Definition of continuity at a point
def func_continuous_at (f : ℝ → ℝ) (a : ℝ) := ∃ b : ℝ, func_converges_to f a (f a)

-- Definition of a continuous function
def func_continuous (f : ℝ → ℝ) := ∀ a : ℝ, func_continuous_at f a

-- Defintion composition of functions and sequences for sequential continuity
def func_seq_comp (f : ℝ → ℝ) (s : ℕ → ℝ) (n : ℕ) := f (s n)

-- Sequential continuity
theorem seq_contin (f : ℝ → ℝ) (a b : ℝ) : (func_converges_to f a b) ↔ ∀ s : ℕ → ℝ, s ⇒ a → func_seq_comp f s ⇒ b :=
begin
    split,
        {intros h s hs ε hε,
        rcases h ε hε with ⟨δ, ⟨hδ, hr⟩⟩,
        cases hs δ hδ with N hN,
        use N, intros n hn,
        have : abs (s n - a) < δ := hN n hn,
        from hr (s n) this
        },
        {intros h,
        cases classical.em (func_converges_to f a b) with ha ha,
        from ha,
        unfold func_converges_to at ha,
        push_neg at ha,
        rcases ha with ⟨ε, ⟨hε, hδ⟩⟩,
        -- let s : ℕ → ℝ := λ n : ℕ, ((hδ (1 / (n + 1)) _) n).some,

        -- have h₁ : s ⇒ a := sorry,
/-        have h₂ : ¬ (func_seq_comp f s ⇒ b) :=
            by {unfold converges_to,
            push_neg, use ε,
            split, from hε,
            intro N, use N + 1,
            split, from nat.le_succ N,
            from hδ (1 / (N + 1)) (zero_le (1 / (N + 1)))

            }
-/
        sorry
        }
end


end M40002