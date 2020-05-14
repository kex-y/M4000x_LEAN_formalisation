-- begin header

import M40002.complete

namespace sequences
-- end header

/- Section
Chapter 3. Sequences
-/

/- Sub-section
Definitions
-/

/-
Let $a : ℕ → ℝ$ be a real valued sequence, then we define convergence of $a$ to some
real $l$ in the standard way.
-/

/- Definition
A real valued sequence $a_n : ℕ → ℝ$ is said to converge to $l ∈ ℝ$ if and only if for all
$ε > 0$, there exists $N ∈ ℕ$ such that for all $n ≥ N$, $\left| a_n - l \right| < ε$. 
-/
def converges_to (a : ℕ → ℝ) (l : ℝ) :=  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (a n - l) < ε 
notation a ` ⇒ ` l := converges_to a l

/- Definition
We call $a_n : ℕ → ℝ$ convergent if there exists $l ∈ ℝ$, $a_n$ converges to $l$.
-/
def is_convergent (a : ℕ → ℝ) := ∃ l : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (a n - l) < ε 

/- Definition
We call $a_n : ℕ → ℝ$ bounede above if and only if there exists $R ∈ ℝ$ such that for all
$n ∈ ℕ$, $a_n ≤ R$.
-/
def seq_bounded_above (a : ℕ → ℝ) := ∃ R : ℝ, ∀ m : ℕ, a m ≤ R

/- Definition
We definte bounded below in a similar way.
-/
def seq_bounded_below (a : ℕ → ℝ) := ∃ R : ℝ, ∀ m : ℕ, R ≤ a m

/- Definition
We call $a_n : ℕ → ℝ$ bounded if and only if it is bounded above and below.
-/
def seq_bounded (a : ℕ → ℝ) := seq_bounded_above a ∧ seq_bounded_below a

def seq_in (a : ℕ → ℝ) (S : set ℝ) := ∀ n : ℕ, a n ∈ S
notation a ` ⊆ ` S := seq_in a S

example (n : ℕ) (hn : 0 < n) : 0 ≤ 1 / n := by exact bot_le

/- Example
Let $a_n : ℕ → ℝ : n ↦ 1 / n$, then $a_n$ converges to 0.
-/
example : (λ n : ℕ, 1 / n) ⇒ 0 :=
begin
  -- We first fix $ε > 0$.
  intros ε hε,
  -- Then by choosing some $N ∈ ℕ$ such that $N > 1 / ε$,
  cases (exists_nat_gt (1 / ε)) with N hN,
  -- we now need to show that for all $n ≥ N$, $\left| a_n - 0 \right| < ε$.
  refine ⟨N, λ n hn, _⟩,
  -- Now as $\left| a_n - 0 \right| = a_n = 1 / n$, it suffices to show that $1 / n < ε$. 
  rw [sub_zero, abs_of_nonneg, (one_div_lt _ hε)], 
    { refine lt_of_lt_of_le hN (by norm_cast; assumption) },
  -- But this follows from the transitivity of inequalities as $1 / n ≤ 1 / N ≤ ε$.
    { refine lt_trans (one_div_pos_of_pos hε) (lt_of_lt_of_le hN (by norm_cast; assumption)) },
    { simp [bot_le] }
end

/- Example
Let $a_n : ℕ → ℝ : n ↦ c$ for some $c ∈ ℝ$. Then $a_n$ converges to $c$
-/
theorem cons_conv {c : ℝ} : (λ n : ℕ, c) ⇒ c :=
begin
  -- Again we fix $ε > 0$
  intros ε hε,
  -- Then by simply choosing our $N = 0$, 
  refine ⟨0, λ n hn, _⟩,
  -- it suffices to show that for all $n ∈ ℕ$, $\left| a_n - c \right| < ε$. 
  -- But $\left| a_n - c \right|$ is simply zero, so we are done!
  simpa
end

/-
We will now prove a very useful lemma that will come up now an again. 
-/

/- Lemma
If $x_0$ and $x_1$ are real numbers such that for all $ε > 0$, $\left| x₀ - x₁ \right| < ε$,
then $x_0 = x_1$.
-/
lemma dist_zero {x₀ x₁ : ℝ}
(h : ∀ (ε : ℝ) (hε : 0 < ε), abs (x₀ - x₁) < ε ) : x₀ = x₁ :=
begin
  -- We will attempt to prove by contradiction, so suppose $x₀ ≠ x₁$.
  apply classical.by_contradiction, intro hne,
  -- Then by trichotomy, either $x₀ < x₁$ or $x₁ < x₀$.
  cases lt_or_gt_of_ne hne with hlt hgt,
  -- If $x₀ < x₁$ then by letting $ε = x₁ - x₀$ we have $\left| x₀ - x₁ \right| < x₀ - x₁$.
    { refine not_le.2 (h (x₁ - x₀) (sub_pos.2 hlt)) _,
  -- But this is a contradiction as for all $r ∈ ℝ$, \left| r \right| ≥ r$.
      rw abs_sub, exact le_abs_self _ },
  -- It's a similar story if $x₁ < x₀$.
    { refine not_le.2 (h (x₀ - x₁) (sub_pos.2 hgt)) ( le_abs_self _) }
end

/-
With that, we will present a short proof that the limits of sequences are unique.
-/

/- Theorem
Let $a_n : ℕ → ℝ$ converge to $b$ and $c$ both of which are real. Then $b = c$. 
-/
theorem unique_lim {a : ℕ → ℝ} {b c : ℝ} (hb : a ⇒ b) (hc : a ⇒ c) : b = c :=
begin
  -- By the previous lemma, it suffices to show that for all $ε > 0, \left| b - c \right| < ε$.
  apply dist_zero, 
  -- So let us fix ε > 0.
  intros ε hε,
  -- Then as $a_n$ converges to $b$, 
  -- there exists some $N₀ ∈ ℕ$ for all $n ≥ N₀, \left a_n - b \right < ε / 2$.
  cases hb (ε / 2) (half_pos hε) with N₀ hN₀,
  -- Similarly there must be some $N₁ ∈ ℕ$ for all $n ≥ N₁, \left a_n - c \right < ε / 2$.
  cases hc (ε / 2) (half_pos hε) with N₁ hN₁,
  -- So let's $N = \max \{N₀, N₁\}$.
  let N := max N₀ N₁,
  -- Then by the triangle inequality, 
  -- we have $\left| b - c \right| ≤ \left| b - a_N \right| + \left| a_N - c \right| < ε / 2 + ε / 2 = ε$.
  apply lt_of_le_of_lt (abs_sub_le b (a N) c),
  linarith [show abs (b - a N) < ε / 2, by rw abs_sub; from hN₀ N (le_max_left _ _), 
  hN₁ N (le_max_right _ _)]
end


#exit

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

-- Defining division of sequences
noncomputable def seq_div_seq (a : ℕ → ℝ) (b : ℕ → ℝ) := λ n : ℕ, (a n) / (b n) 
noncomputable instance : has_div (ℕ → ℝ) := ⟨seq_div_seq⟩

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
theorem sandwich {a b c : ℕ → ℝ} {l : ℝ} (h₀ : a ⇒ l) (h₁ : c ⇒ l) : (a ≤* b) ∧ (b ≤* c) → b ⇒ l :=
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

end sequences