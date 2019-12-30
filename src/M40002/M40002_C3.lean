-- M40002 (Analysis I) Chapter 3. Sequences

import M40002.M40002_C2

namespace M40002

-- Defintions for convergent sequences

def converges_to (a : ℕ → ℝ) (l : ℝ) :=  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (a n - l) < ε 
notation a ` ⇒ ` l := converges_to a l

def is_convergent (a : ℕ → ℝ) := ∃ l : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (a n - l) < ε 

def seq_bounded_above (a : ℕ → ℝ) := ∃ R : ℝ, ∀ m : ℕ, a m ≤ R
def seq_bounded_below (a : ℕ → ℝ) := ∃ R : ℝ, ∀ m : ℕ, R ≤ a m

def seq_bounded (a : ℕ → ℝ) := seq_bounded_above a ∧ seq_bounded_below a

-- Example 3.4 (1 / n → 0)
example (a : ℕ → ℝ) (ha : a = λ n : ℕ, 1 / n) : a ⇒ 0 :=
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
example (a : ℕ → ℝ) (ha : a = λ n : ℕ, (n + 5) / (n + 1)) : a ⇒ 1 :=
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
    repeat {sorry} -- I can't bring myself to complete this proof!
end

-- Limits are unique! (I gotta admit this my proof is very terrible with alot of unnecessary lines :/)
theorem unique_lim (a : ℕ → ℝ) (b c : ℝ) (hb : a ⇒ b) (hc : a ⇒ c) : b = c :=
begin
    have : ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (b - c) < ε) :=
        by {intros ε hε,
        cases hb (ε / 2) (half_pos hε) with N₁ hN₁,
        cases hc (ε / 2) (half_pos hε) with N₂ hN₂,
        use max N₁ N₂,
        intros n hn,
        have : N₁ ≤ n ∧ N₂ ≤ n := 
                by {split, 
                    {apply le_trans (le_max_left N₁ N₂), rwa ge_from_le at hn},
                    {apply le_trans (le_max_right N₁ N₂), rwa ge_from_le at hn}
                    },
        replace hb : abs (a n - b) < (ε / 2) := hN₁ n this.left,
        replace hc : abs (a n - c) < (ε / 2) := hN₂ n this.right,
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

-- If (a n) is convergent then its bounded
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

/- Can I define the addition of sequences through instances?
def seq := ℕ → ℝ

def seq_add : seq → seq → seq

instance seq_has_add : has_add seq := apply_instance
-/

-- Defining addition for sequences
def seq_add_seq (a : ℕ → ℝ) (b : ℕ → ℝ) := λ n : ℕ, a n + b n
notation a ` + ` b := seq_add_seq a b

def seq_add_real (a : ℕ → ℝ) (b : ℝ) := λ n : ℕ, a n + b
notation a ` + ` b := seq_add_real a b

-- Algebra of limits
theorem add_lim_conv (a b : ℕ → ℝ) (l m : ℝ) : a ⇒ l ∧ b ⇒ m → (a + b) ⇒ (l + m) :=
begin
    rintros ⟨ha, hb⟩ ε hε,
    have : ε / 2 > 0 := half_pos hε,
    cases ha (ε / 2) this with N₁ hN₁,
    cases hb (ε / 2) this with N₂ hN₂,
    let N : ℕ := max N₁ N₂,
    use N,
    intros n hn,
    have hrw : a n + b n - (l + m) = (a n - l) + (b n - m) := by {linarith},
    unfold seq_add_seq,
    rw hrw,
    have hmax : N ≥ N₁ ∧ N ≥ N₂ := 
        by {split,
            all_goals {rwa [ge_iff_le, le_max_iff], tauto}},
    suffices h : abs (a n - l) + abs (b n - m) < ε,
        from lt_of_le_of_lt (abs_add (a n - l) (b n - m)) h,
    have h : abs (a n - l) + abs (b n - m) < ε / 2 + ε / 2 := 
        by {from add_lt_add (hN₁ n (ge_trans hn hmax.left)) (hN₂ n (ge_trans hn hmax.right))},
    rwa add_halves' ε at h
end
 
lemma diff_seq_is_zero (a b : ℕ → ℝ) (l : ℝ) (h : a ⇒ l) : a = b + l → b ⇒ 0 :=
begin
    unfold seq_add_real, unfold converges_to,
    unfold converges_to at h,
    intro ha,
    rw ha at h, simp at h,
    suffices : ∀ (ε : ℝ), 0 < ε → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → abs (b n) < ε),
        simpa,
    assumption
end

-- Defining multiplication of sequences
def seq_mul_seq (a : ℕ → ℝ) (b : ℕ → ℝ) := λ n : ℕ, a n * b n
notation a ` × ` b := seq_mul_seq a b

def seq_mul_real (a : ℕ → ℝ) (b : ℝ) := λ n : ℕ, a n * b
notation a ` × ` b := seq_mul_real a b

theorem mul_lim_conv (a b : ℕ → ℝ) (l m : ℝ) (ha : a ⇒ l) (hb : b ⇒ m) : (a × b) ⇒ l * m :=
begin
    sorry
end

-- Defining division of sequences (why is this noncomputable?)
noncomputable def seq_div_seq (a : ℕ → ℝ) (b : ℕ → ℝ) := λ n : ℕ, (a n) / (b n) 
notation a ` / ` b := seq_div_seq a b

noncomputable def seq_div_real (a : ℕ → ℝ) (b : ℝ) := λ n : ℕ, a n / b
notation a ` / ` b := seq_div_real a b

theorem div_lim_conv (a b : ℕ → ℝ) (l m : ℝ) (ha : a ⇒ l) (hb : b ⇒ m) (hc : m ≠ 0) : (a / b) ⇒ l / m :=
begin
    sorry
end

-- Defining monotone increasing and decreasing sequences
def mono_increasing (a : ℕ → ℝ) := ∀ n : ℕ, a n ≤ a (n + 1)
notation a ` ↑ ` := mono_increasing a

def strict_mono_increasing (a : ℕ → ℝ) := ∀ n : ℕ, a n < a (n + 1)
notation a ` ↑* ` := strict_mono_increasing a

def mono_increasing_conv (a : ℕ → ℝ) (l : ℝ) := mono_increasing a ∧ a ⇒ l
notation a ` ↑ ` l := mono_increasing a l

def mono_decreasing (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) ≤ a n
notation a ` ↓ ` := mono_decreasing a

def strict_mono_decreasing (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) < a n
notation a ` ↓* ` := strict_mono_decreasing a

def mono_decreasing_conv (a : ℕ → ℝ) (l : ℝ) := mono_decreasing a ∧ a ⇒ l
notation a ` ↓ ` l := mono_decreasing a l

lemma le_chain (N : ℕ) (b : ℕ → ℝ) (h : mono_increasing b) : ∀ n : ℕ, N ≤ n → b N ≤ b n :=
begin
    intros n hn,
    have ha : ∀ k : ℕ, b N ≤ b (N + k) :=
        by {intro k,
        induction k with k hk,
            {refl},
            {from le_trans hk (h (N + k))}
        },
    have : ∃ k : ℕ, N + k = n := nat.le.dest hn,
    cases this with k hk,
    rw ←hk,
    from ha k
end

lemma ge_chain (N : ℕ) (b : ℕ → ℝ) (h : mono_decreasing b) : ∀ n : ℕ, N ≤ n → b n ≤ b N :=
begin
    intros n hn,
    have ha : ∀ k : ℕ, b (N + k) ≤ b N :=
        by {intro k,
        induction k with k hk,
            {refl},
            {from le_trans (h (N + k)) hk}
        },
    have : ∃ k : ℕ, N + k = n := nat.le.dest hn,
    cases this with k hk,
    rw ←hk,
    from ha k
end

-- Monotone increasing and bounded means convergent (to the supremum)
lemma mono_increasing_means_conv_sup (b : ℕ → ℝ) (M : ℝ) (h₁ : mono_increasing b) (h₂ : seq_bounded b) (h₃ : sup {t : ℝ | ∃ n : ℕ, t = b n} M) : b ⇒ M :=
begin
    rcases h₂ with ⟨⟨N, habv⟩, hblw⟩,
    intros ε hε,
    clear habv N,
    have : ∃ N : ℕ, M - ε < b N :=
        by {cases h₃ with hubd hnubd,
        unfold upper_bound at hnubd,
        push_neg at hnubd,
        have : M - ε < M := 
            by {rw gt_iff_lt at hε,
            from sub_lt_self M hε},
        rcases hnubd (M - ε) this with ⟨s, ⟨hs₁, hs₂⟩⟩,
        rw set.mem_set_of_eq at hs₁,
        cases hs₁ with n hn,
        use n, rwa ←hn
        },
    cases this with N hN,
    use N, intros n hn,
    rw abs_of_nonpos,
        {have : ∀ n : ℕ, N ≤ n → b N ≤ b n := le_chain N b h₁,
        suffices : M - ε < b n,
            simp, from sub_lt.mp this,
        from lt_of_lt_of_le hN (this n (iff.rfl.mp hn))
        },
        cases h₃,
        have : b n ≤ M := by {apply h₃_left, rwa set.mem_set_of_eq, use n},
        from sub_nonpos_of_le this
end

theorem mono_increasing_means_conv (b : ℕ → ℝ) (h₁ : mono_increasing b) (h₂ : seq_bounded b) : is_convergent b :=
begin
    let α : set ℝ := {t : ℝ | ∃ n : ℕ, t = b n},
    have : ∃ M : ℝ, sup α M :=
        by {rcases h₂ with ⟨⟨R, habv⟩, hblw⟩,
            apply completeness α,
            {use R, rintros s ⟨n, hs⟩,
            suffices : b n ≤ R, rwa ←hs at this,
            from habv n
            },
            {suffices : b 0 ∈ α,
                apply set.not_eq_empty_iff_exists.mpr,
                use b 0, assumption,
            rw set.mem_set_of_eq,
            use 0
            }        
        },
    cases this with M hM,
    use M,
    from mono_increasing_means_conv_sup b M h₁ h₂ hM
end

-- Monotone decreasing and bounded means convergent (to the infimum)
lemma mono_decreasing_means_conv_inf (b : ℕ → ℝ) (M : ℝ) (h₁ : mono_decreasing b) (h₂ : seq_bounded b) (h₃ : inf {t : ℝ | ∃ n : ℕ, t = b n} M) : b ⇒ M :=
begin
    intros ε hε,
    have : ∃ N : ℕ, b N < M + ε :=
        by {cases h₃ with hlbd hnlbd,
        unfold lower_bound at hnlbd,
        push_neg at hnlbd,
        have : M < M + ε := by {linarith},
        rcases hnlbd (M + ε) this with ⟨s, ⟨hs₁, hs₂⟩⟩,
        rw set.mem_set_of_eq at hs₁,
        cases hs₁ with n hn,
        use n, rwa ←hn
        },
    cases this with N hN,
    use N, intros n hn,
    rw abs_lt, split,
        {suffices : M - ε < b n, linarith,
        have : M ≤ b n := by {apply h₃.left (b n), rw set.mem_set_of_eq, use n},
        have hα : M - ε < M := by {linarith},
        from lt_of_lt_of_le hα this
        },
        {suffices : b n < M + ε, linarith,
        from lt_of_le_of_lt (ge_chain N b h₁ n (iff.rfl.mp hn)) hN
        }
end 

theorem mono_decreasing_means_conv (b : ℕ → ℝ) (h₁ : mono_decreasing b) (h₂ : seq_bounded b) : is_convergent b :=
begin
    let α : set ℝ := {t : ℝ | ∃ n : ℕ, t = b n},
    have : ∃ M : ℝ, inf α M :=
        by {rcases h₂ with ⟨habv, ⟨R, hblw⟩⟩,
            apply completeness_below α,
            {use R, rintros s ⟨n, hs⟩,
            rw hs,
            from hblw n
            },
            {suffices : b 0 ∈ α,
                apply set.not_eq_empty_iff_exists.mpr,
                use b 0, assumption,
            rw set.mem_set_of_eq,
            use 0
            }        
        },
    cases this with M hM,
    use M,
    from mono_decreasing_means_conv_inf b M h₁ h₂ hM
end

-- Defining order on sequences (is this necessary?)
def le_seq (a b : ℕ → ℝ) := ∀ n : ℕ, a n ≤ b n
notation a ` ≤* ` b := le_seq a b

def lt_seq (a b : ℕ → ℝ) := ∀ n : ℕ, a n < b n
notation a ` <* ` b := lt_seq a b

def ge_seq (a b : ℕ → ℝ) := ∀ n : ℕ, a n ≥ b n
notation a ` ≥* ` b := ge_seq a b

def gt_seq (a b : ℕ → ℝ) := ∀ n : ℕ, a n > b n
notation a ` >* ` b := gt_seq a b

-- Comparison of sequences
theorem le_lim (a b : ℕ → ℝ) (l m : ℝ) (ha : a ⇒ l) (hb : b ⇒ m) : (a ≤* b) → l ≤ m :=
begin
    rw ←not_lt,
    intros h hlt,
    have hδ : (l - m) / 2 > 0 := half_pos (sub_pos.mpr hlt),
    cases ha ((l - m) / 2) hδ with N₁ hN₁,
    cases hb ((l - m) / 2) hδ with N₂ hN₂,
    let N := max N₁ N₂,
    have hmax : N ≥ N₁ ∧ N ≥ N₂ := 
        by {split,
            all_goals {rwa [ge_iff_le, le_max_iff], tauto}},
    replace hN₁ : abs (a N - l) < (l - m) / 2 := hN₁ N hmax.left,
    replace hN₂ : abs (b N - m) < (l - m) / 2 := hN₂ N hmax.right,
    have hα : (l + m) / 2 < a N := 
        by {rw abs_lt at hN₁,
        cases hN₁ with hl hr,
        linarith
        },
    have hβ : b N < (l + m) / 2 := 
        by {rw abs_lt at hN₂,
        cases hN₂ with hl hr,
        linarith
        },
    have : b N < a N := lt_trans hβ hα,
    rw ←not_le at this,
    from this (h N)
end

-- Cauchy Sequences
def cauchy (a : ℕ → ℝ) := ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n ∧ N ≤ m → abs (a n - a m) < ε

-- Convergent implies Cauchy
lemma conv_to_cauchy (a : ℕ → ℝ) (h : is_convergent a) : cauchy a :=
begin
    cases h with l hl,
    intros ε hε,
    cases hl (ε / 2) (half_pos hε) with N hN,
    use N, intros n m hnm,
    suffices : abs (a n - l) + abs (a m - l) < ε,
        {rw abs_sub (a m) l at this,
        have h : abs (a n - l + (l - a m)) < ε :=
            lt_of_le_of_lt (abs_add_le_abs_add_abs (a n - l) (l - a m)) this,
        rwa sub_add_sub_cancel (a n) l (a m) at h
        },
    have h : abs (a n - l) + abs (a m - l) < ε / 2 + ε / 2 := 
        add_lt_add (hN n hnm.left) (hN m hnm.right),
    linarith        
end

-- Cauchy implies bounded
lemma cauchy_bounded (a : ℕ → ℝ) : cauchy a → seq_bounded a := by sorry

-- Cauchy implies convergent
lemma cauchy_to_conv (a : ℕ → ℝ) (h : cauchy a) : is_convergent a :=
begin
-- Since a is Cauchy, it is bounded above
    rcases (cauchy_bounded a h) with ⟨⟨R₀, hn⟩, ⟨R₁, hnn⟩⟩,
-- Let's construct the sequence b where b n = sup {a i | i ≥ n}
-- We first need to show such supremums exists for all n
    have : ∀ m : ℕ, ∃ α : ℝ, sup {t : ℝ | ∃ i : ℕ, m ≤ i ∧ t = a i} α :=
        by {intro m,
        have hα : bounded_above {t : ℝ | ∃ i : ℕ, m ≤ i ∧ t = a i} :=
            by {use R₀, intros s hs,
            rw set.mem_set_of_eq at hs,
            rcases hs with ⟨i, ⟨hi₁, hi₂⟩⟩,
            rw hi₂, from hn i
            },
        have hβ : {t : ℝ | ∃ i : ℕ, m ≤ i ∧ t = a i} ≠ ∅ :=
            by {dsimp, rw set.not_eq_empty_iff_exists,
            use a (m + 1), dsimp,
            use m + 1, finish
            },
        from completeness {t : ℝ | ∃ i : ℕ, m ≤ i ∧ t = a i} hα hβ
        },
-- Now we construct b
    let b : ℕ → ℝ := λ n, classical.some (this n),
    have hα : mono_decreasing b :=
        by {unfold mono_decreasing, --delete this
        intro n,
        sorry
        },
    have hβ : seq_bounded b :=
        by {split,
            {use R₀, intro m, sorry},
            {use R₁, intro m, sorry}
        },
-- Since b (by construction) is monotonically decreasing and bounded, we have it converges to its infimum
    cases mono_decreasing_means_conv b hα hβ with l hl,
-- I claim that this is what a converges to also!
    use l, intros ε hε,
    unfold cauchy at h,
    cases h (ε / 2) (half_pos hε) with N hN,
    use N, intros n hn',
    sorry 
-- under construction
end

-- Cauchy iff. convergent
theorem cauchy_iff_conv {a : ℕ → ℝ} : cauchy a ↔ is_convergent a :=
begin
    split,
        {intro h, from cauchy_to_conv a h},
        {intro h, from conv_to_cauchy a h}
end

--set_option trace.simplify.rewrite true
--example (a b c : ℝ) : a - b + (b - c) = a - c := by {library_search}


end M40002