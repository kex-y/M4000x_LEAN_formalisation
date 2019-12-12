-- M40002 (Analysis I) Chapter 3. Sequences

import data.real.basic
import M40001.M40001_4

namespace M40002

variables {X Y : Type}

-- Defintions for sequences

def converges_to (a : ℕ → ℝ) (l : ℝ) :=  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (a n - l) < ε 
infix ` ~> `: 50 := converges_to

-- Example 3.4
example (a : ℕ → ℝ) (ha : a = λ n : ℕ, 1/n) : a ~> 0 :=
begin
    intros ε hε,
    have : ∃ N : ℕ, (1 / (N + 1) : ℝ) < ε := exists_nat_one_div_lt hε,
    cases this with N hN,
        use (N + 1),
    intros n hn,
    simp,
    have hb : 0 ≤ a n := by {rw ha, simp},
    have : abs (a n) = a n := by {exact abs_of_nonneg hb},
    rw [this, ha], dsimp,
    have hc : (1 / n : ℝ) ≤ (1 / (N + 1) : ℝ) := 
        by {apply div_le_div_of_le_left,
            {linarith},
            {have hd : 0 ≤ (N : ℝ) := nat.cast_nonneg N,
            linarith
            },
            {rw ge_from_le at hn,
            norm_cast, assumption
            },
        },
    rw le_iff_lt_or_eq at hc,
    cases hc,
        {from lt_trans hc hN},
        {rwa hc}
end

-- Example 3.5
example (a : ℕ → ℝ) (ha : a = λ n : ℕ, (n + 5) / (n + 1)) : a ~> 1 :=
begin
    intros ε hε,
    have : ∃ N : ℕ, (4 / N : ℝ) < ε :=
        by {cases exists_nat_one_div_lt hε with M hM,
        use (4 * (M + 1)),
        suffices : 4 / (4 * (↑M + 1)) < ε,
          exact_mod_cast this,
        have : (4 : ℝ) ≠ 0 := by linarith,
        rwa (div_mul_right (↑M + 1 : ℝ) this),
        },
    cases this with N hN,
    use N, intros n hn,
    have h0 : 0 ≤ a n - 1 :=
        by {rw ha, simp,
        rw (show (5 + ↑n :ℝ) = 4 + 1 + ↑n, by linarith),
        rw [add_assoc, add_div, div_self], 
        suffices : (0 : ℝ) ≤ 4 / (1 + ↑n),
          simpa using this,
        refine le_of_lt (div_pos (by linarith) _),
        repeat {norm_cast, linarith},
        }
end


end M40002