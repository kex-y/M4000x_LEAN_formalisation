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
lemma converge_is_bdd_abv (b : ℕ → ℝ) : is_convergent b → seq_bounded_above b :=
begin
    rintro ⟨l, hl⟩,
    cases (hl 1 _) with N hN,
    swap, linarith,
    let U := finset.image b (finset.range (N + 1)) ∪ {l + 1},
    have : b 0 ∈ U := by simp,  
    cases finset.max_of_mem this with R hR,
    use R, intro m,
    cases le_or_lt m N,
        {have : b m ∈ U :=
            by{simp, left, use m, from ⟨(nat_le_imp_lt_succ N m).mp h, rfl⟩},
        from finset.le_max_of_mem this hR
        },
        {have : l + 1 ∈ U := by {simp},
        replace this : l + 1 ≤ R :=
            by {from finset.le_max_of_mem this hR},
        apply le_trans _ this,
        replace this : abs (b m - l) < 1 := hN m (le_of_lt h),
        rw abs_lt at this,
        from le_of_lt (sub_lt_iff_lt_add'.mp this.right)
        }
end

lemma converge_is_bdd_blw (b : ℕ → ℝ) : is_convergent b → seq_bounded_below b :=
begin
    rintro ⟨l, hl⟩,
    cases (hl 1 _) with N hN,
    swap, linarith,
    let U := finset.image b (finset.range (N + 1)) ∪ {l + -1},
    have : b 0 ∈ U := by simp,  
    cases finset.min_of_mem this with R hR,
    use R, intro m,
    cases le_or_lt m N,
        {have : b m ∈ U :=
            by{simp, left, use m, from ⟨(nat_le_imp_lt_succ N m).mp h, rfl⟩},
        from finset.min_le_of_mem this hR
        },
        {have : l + -1 ∈ U := by {simp},
        replace this : R ≤ l + -1 :=
            by {from finset.min_le_of_mem this hR},
        apply le_trans this,
        replace this : abs (b m - l) < 1 := hN m (le_of_lt h),
        rw abs_lt at this,
        from le_of_lt (lt_sub_iff_add_lt'.mp this.left)
        }
end

theorem converge_is_bdd (b : ℕ → ℝ) : is_convergent b → seq_bounded b := λ h, ⟨converge_is_bdd_abv b h, converge_is_bdd_blw b h⟩

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

def mono_increasing_conv (a : ℕ → ℝ) (l : ℝ) := mono_increasing a ∧ a ⇒ l
notation a ` ↑ ` l := mono_increasing a l

def mono_decreasing (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) ≤ a n
notation a ` ↓ ` := mono_decreasing a

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

-- Sandwich Theorem. Suppose that an ≤ bn ≤ cn ∀n and that an → a and cn → a, Then bn → a.
theorem sandwich_theorem {a b c : ℕ → ℝ} {l : ℝ} (h₀ : a ⇒ l) (h₁ : c ⇒ l) : (a ≤* b) ∧ (b ≤* c) → b ⇒ l :=
begin
    rintro ⟨ha, hb⟩,
    intros ε hε,
    cases (h₀ ε hε) with N₀ hN₀,
    cases (h₁ ε hε) with N₁ hN₁,
    let N := max N₀ N₁,
    have hN : N₀ ≤ N ∧ N₁ ≤ N := by {finish},
    use N,
    intros n hn,
    cases lt_or_ge (b n) l with hlt hge,
        {rw [abs_sub, abs_of_pos (sub_pos.mpr hlt)],
        apply lt_of_le_of_lt _ (hN₀ n (le_trans hN.left hn)),
        apply le_trans ((sub_le_sub_iff_left l).mpr (ha n)) _,
        rw abs_sub,
        from le_abs_self (l - a n)
        },
        {rw abs_of_nonneg (sub_nonneg.mpr hge),
        apply lt_of_le_of_lt _ (hN₁ n (le_trans hN.right hn)),
        apply le_trans (add_le_add_right' (hb n)) _,
        from le_abs_self (c n - l)
        }
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

-- We will prove that Cauchy implies bounded after subsequences!

-- Subsequences
def is_subseq (a b : ℕ → ℝ) := ∃ n : ℕ → ℕ, (strict_mono n ∧ ∀ i : ℕ, b i = a (n i))

-- b n = 1 is a subsequence of a n = (-1)^ n
example (a b : ℕ → ℝ) (h₁ : a = λ i, (- 1)^ i) (h₂ : b = λ i, 1) : is_subseq a b :=
begin
    let n := λ i, 2 * i,
    unfold is_subseq,
    use n, split,
        {intros a b, finish},
        {intro i,
        have : n = λ (i : ℕ), 2 * i, refl, 
        rwa [h₁, h₂, this], simp,
        rw pow_mul, 
        finish
        }
end

-- Every sequence has atleast one subsequence
theorem has_subseq (a : ℕ → ℝ) : ∃ b : ℕ → ℝ, is_subseq a b :=
begin
    use a,
    unfold is_subseq,
    let n : ℕ → ℕ := λ i, i,
    have : n = λ i, i := rfl,
    use n, split,
        {intros a b hab,
        rw this, simpa
        },
        {intro i,
        rwa this,
        }
end

-- n(i) ≥ i ∀ i ∈ ℕ
lemma subseq_ge_id {n : ℕ → ℕ} (h : strict_mono n) : ∀ i : ℕ, i ≤ n i :=
begin
    intro i,
    induction i with i hi,
        {from zero_le (n 0)},
        {have : (n i) + 1 ≤ n (nat.succ i) :=
            by {rw nat.succ_le_iff,
            from h (lt_add_one i)
            },
        from le_trans (nat.pred_le_iff.mp hi) this
        }
end

-- Bolzano-Weierstrass : Every bounded sequence has a convergent subsequence
theorem bolzano_weierstrass {a : ℕ → ℝ} (h₁ : seq_bounded a) : ∃ b : ℕ → ℝ, is_subseq a b ∧ is_convergent b :=
begin
    sorry
end

-- a → l iff. all subsequences of a also converges to l
theorem conv_subseq {a : ℕ → ℝ} {l : ℝ} : a ⇒ l ↔ (∀ b : ℕ → ℝ, is_subseq a b → b ⇒ l) :=
begin
    split,
        {rintros h b ⟨n, ⟨hn₁, hn₂⟩⟩ ε hε,
        cases (h ε hε) with N hN,
        use N, intros i hi,
        rw hn₂ i,
        have : n i ≥ N := ge_trans (subseq_ge_id hn₁ i) hi,
        from hN (n i) this
        },
        {intro h,
        let n : ℕ → ℕ := λ i, i,
        let b : ℕ → ℝ := a,
        have : is_subseq a b :=
            by {use n, split,
            have : n = λ i, i := rfl,
                {intros a b hab,
                rw this, simpa},
                {simp},
            },
        have ha : a = b := rfl,
        rw ha, from h b this
        }
end

-- Cauchy implies bounded
lemma cauchy_bounded_abv (b : ℕ → ℝ) : cauchy b → seq_bounded_above b :=
begin
    intro hb,
    cases (hb 1 _) with N hN,
    swap, linarith,
    let U := finset.image b (finset.range (N + 1)) ∪ {b N + 1},
    have : b 0 ∈ U := by simp,  
    cases finset.max_of_mem this with R hR,
    use R, intro m,
    cases le_or_lt m N,
        {have : b m ∈ U :=
            by{simp, left, use m, from ⟨(nat_le_imp_lt_succ N m).mp h, rfl⟩},
        from finset.le_max_of_mem this hR
        },
        {have : b N + 1 ∈ U := by {simp},
        replace this : b N + 1 ≤ R :=
            by {from finset.le_max_of_mem this hR},
        apply le_trans _ this,
        replace this : abs (b m - b N) < 1 := hN m N ⟨le_of_lt h, le_refl N⟩,
        rw abs_lt at this,
        from le_of_lt (sub_lt_iff_lt_add'.mp this.right)
        }
end

lemma cauchy_bounded_blw (b : ℕ → ℝ) : cauchy b → seq_bounded_below b :=
begin
    intro hb,
    cases (hb 1 _) with N hN,
    swap, linarith,
    let U := finset.image b (finset.range (N + 1)) ∪ {b N + -1},
    have : b 0 ∈ U := by simp,  
    cases finset.min_of_mem this with R hR,
    use R, intro m,
    cases le_or_lt m N,
        {have : b m ∈ U :=
            by{simp, left, use m, from ⟨(nat_le_imp_lt_succ N m).mp h, rfl⟩},
        from finset.min_le_of_mem this hR
        },
        {have : b N + -1 ∈ U := by {simp},
        replace this : R ≤ b N + -1 :=
            by {from finset.min_le_of_mem this hR},
        apply le_trans this,
        replace this : abs (b m - b N) < 1 := hN m N ⟨le_of_lt h, le_refl N⟩,
        rw abs_lt at this,
        from le_of_lt (lt_sub_iff_add_lt'.mp this.left)
        }
end


lemma cauchy_bounded (a : ℕ → ℝ) : cauchy a → seq_bounded a := λ h, ⟨cauchy_bounded_abv a h, cauchy_bounded_blw a h⟩

-- Cauchy implies convergent
lemma cauchy_to_conv (a : ℕ → ℝ) (h : cauchy a) : is_convergent a :=
begin
    rcases bolzano_weierstrass (cauchy_bounded a h) with ⟨b, ⟨⟨n, ⟨hb₁, hb₂⟩⟩, ⟨l, hl⟩⟩⟩,
    use l, intros ε hε,
    cases h (ε / 2) (half_pos hε) with N₁ hN₁,
    cases hl (ε / 2) (half_pos hε) with N₂ hN₂,
    let N := n (max N₁ N₂),
    use N, intros i hi,
    suffices : abs (a i - a N) + abs (a N - l) < ε,
        apply lt_of_le_of_lt _ this,
        have hβ: a i - a N + (a N - l) = a i - l := by {linarith},
        rw ←hβ,
        from abs_add (a i - a N) (a N - l),
    have hα : abs (a i - a N) + abs (a N - l) < ε / 2 + ε / 2 := 
        by {have : N = n (max N₁ N₂) := rfl,
            apply add_lt_add,
            {have hβ : N₁ ≤ N :=
                by {rw this, from le_trans (le_max_left N₁ N₂) (subseq_ge_id hb₁ (max N₁ N₂))},
            have hγ : N₁ ≤ i := by {from le_trans hβ hi},
            from hN₁ i N ⟨hγ, hβ⟩
            },
            {have hβ : N₂ ≤ N :=
                by {rw this, from le_trans (le_max_right N₁ N₂) (subseq_ge_id hb₁ (max N₁ N₂))},
            apply lt_of_le_of_lt _ (hN₂ (max N₁ N₂) (le_max_right N₁ N₂)),
            rwa hb₂ (max N₁ N₂)
            }
        },
    linarith
end

-- Cauchy iff. convergent
theorem cauchy_iff_conv {a : ℕ → ℝ} : cauchy a ↔ is_convergent a :=
begin
    split,
        {intro h, from cauchy_to_conv a h},
        {intro h, from conv_to_cauchy a h}
end

end M40002