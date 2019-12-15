-- M40002 (Analysis I) Chapter 3. Sequences

import data.real.basic
import M40002.M40002_C2

namespace M40002

variables {X Y : Type}

-- Defintions for convergent sequences

def converges_to (a : ℕ → ℝ) (l : ℝ) :=  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (a n - l) < ε 
infix ` ~> `: 50 := converges_to

def is_convergent (a : ℕ → ℝ) := ∃ l : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (a n - l) < ε 

def seq_bounded_above (a : ℕ → ℝ) := ∃ n : ℕ, ∀ m : ℕ, a m ≤ a n
def seq_bounded_below (a : ℕ → ℝ) := ∃ n : ℕ, ∀ m : ℕ, a n ≤ a m

def seq_bounded (a : ℕ → ℝ) := seq_bounded_above a ∧ seq_bounded_below a

-- Example 3.4 (1 / n → 0)
example (a : ℕ → ℝ) (ha : a = λ n : ℕ, 1 / n) : a ~> 0 :=
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

-- Example 3.5 ((n + 5) / (n + 1) → 1)
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
        },
    rw [abs_of_nonneg h0, ha],
    suffices : (5 + ↑n) / (1 + ↑n) - 1 < ε,
        simpa using this,
    rw (show (5 + ↑n :ℝ) = 4 + 1 + ↑n, by linarith),
    rw [add_assoc, add_div, div_self], 
    {suffices : 4 / (1 + ↑n) < ε,
        simpa using this,
    have : 1 / (1 + n) ≤ 1 / N :=
        by {sorry},
    sorry,
    },
    sorry, -- Terribly sorry but I can't bring myself to complete this proof!
end

--set_option trace.simplify.rewrite true
-- Limits are unique!
theorem unique_lim (a : ℕ → ℝ) (b c : ℝ) (hb : a ~> b) (hc : a ~> c) : b = c :=
begin
    have : ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (b - c) < ε) :=
        by {intros ε hε,
        cases hb (ε / 2) (half_pos hε) with N1 hN1,
        cases hc (ε / 2) (half_pos hε) with N2 hN2,
        use max N1 N2,
        intros n hn,
        have : N1 ≤ n ∧ N2 ≤ n := 
                by {split, 
                    {apply le_trans (le_max_left N1 N2), rwa ge_from_le at hn},
                    {apply le_trans (le_max_right N1 N2), rwa ge_from_le at hn}
                    },
        replace hb : abs (a n - b) < (ε / 2) := hN1 n this.left,
        replace hc : abs (a n - c) < (ε / 2) := hN2 n this.right,
        rwa abs_sub (a n) b at hb,
        suffices : abs (b - (a n) + (a n) - c) < ε,
            by {simp at this, from this},
        have hd : abs (a n - c) + abs (b - a n) < ε / 2 + ε / 2 := add_lt_add hc hb,
        simp at hd,
        have he : abs (b -a n + a n + -c) ≤ abs (b + -a n) + abs (a n + -c) :=
            by {suffices : abs (b + -a n + (a n + -c)) ≤ abs (b + -a n) + abs (a n + -c),
                    simp at this, rwa [sub_eq_add_neg b (a n), neg_add_cancel_right b (a n)],
                from abs_add (b + -a n) (a n + -c)},
        apply lt_of_le_of_lt he hd
        },
    have ha : ∀ (ε : ℝ), ε > 0 →  abs (b - c) < ε :=
        by {intros ε hε,
        cases this ε hε with N hN,
        have ha : N + 1 ≥ N := by {linarith},
        from hN (N + 1) ha
        },
    rwa ←(equality_def c b)
end

-- If (a n) is convergent then its bounded!
theorem converge_is_bdd (a : ℕ → ℝ) : is_convergent a → seq_bounded a :=
begin
    unfold is_convergent,
    unfold seq_bounded,
    unfold seq_bounded_above,
    unfold seq_bounded_below,
    rintro ⟨l, hl⟩,
    have : (1 : ℝ) > 0 := by {linarith},
    -- Note that we have (hl 1 this) == ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (a n - l) < 1
    -- then we can let the bound be max {a 1, a 2, ... , a (N - 1), l + 1}
    -- But how can I type this in LEAN I've got no idea! :/
    sorry
end


end M40002