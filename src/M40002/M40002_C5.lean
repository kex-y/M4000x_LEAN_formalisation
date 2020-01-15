-- M40002 (Analysis I) Chapter 5. Continuity

import M40002.M40002_C4

namespace M40002

-- Definition of limits of functions (f(x) → b as x → a)
def func_converges_to (f : ℝ → ℝ) (a b : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs (x - a) < δ → abs (f x - b) < ε

-- Definition of continuity at a point
def func_continuous_at (f : ℝ → ℝ) (a : ℝ) := func_converges_to f a (f a)

-- Definition of a continuous function
def func_continuous (f : ℝ → ℝ) := ∀ a : ℝ, func_continuous_at f a

-- Defintion composition of functions and sequences for sequential continuity
def func_seq_comp (f : ℝ → ℝ) (s : ℕ → ℝ) (n : ℕ) := f (s n)

-- Sequential continuity
theorem seq_contin {f : ℝ → ℝ} {a b : ℝ} : (func_converges_to f a b) ↔ ∀ s : ℕ → ℝ, s ⇒ a → func_seq_comp f s ⇒ b :=
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

-- Algebra of limits for functions
def func_add_func (f g : ℝ → ℝ) := λ r : ℝ, f r + g r
notation f ` + ` g := func_add_func f g

theorem func_add_lim_conv (f g : ℝ → ℝ) (a b₁ b₂) : func_converges_to f a b₁ ∧ func_converges_to g a b₂ → func_converges_to (f + g) a (b₁ + b₂) :=
begin
	rintro ⟨ha, hb⟩,
	rw seq_contin,
	intros s hs,
	have : func_seq_comp (f + g) s = func_seq_comp f s + func_seq_comp g s := rfl,
	rw this,
	apply add_lim_conv,
	from ⟨seq_contin.mp ha s hs, seq_contin.mp hb s hs⟩
end

def func_mul_func (f g : ℝ → ℝ) := λ r : ℝ, f r * g r
notation f ` × ` g := func_mul_func f g

theorem func_mul_func_conv (f g : ℝ → ℝ) (a b₁ b₂) : func_converges_to f a b₁ ∧ func_converges_to g a b₂ → func_converges_to (f × g) a (b₁ * b₂) :=
begin
	rintro ⟨ha, hb⟩,
	rw seq_contin,
	intros s hs,
	have : func_seq_comp (f × g) s = seq_mul_seq (func_seq_comp f s) (func_seq_comp g s) := rfl,
	rw this,
	apply mul_lim_conv,
	from seq_contin.mp ha s hs,
	from seq_contin.mp hb s hs,
end

noncomputable def func_div_func (f g : ℝ → ℝ) := λ r : ℝ, (f r) / (g r)
notation f ` / ` g := func_div_func f g

theorem func_div_func_conv (f g : ℝ → ℝ) (a b₁ b₂) (h : b₂ ≠ 0) : func_converges_to f a b₁ ∧ func_converges_to g a b₂ → func_converges_to (f / g) a (b₁ / b₂) :=
begin
	rintro ⟨ha, hb⟩,
	rw seq_contin,
	intros s hs,
	have : func_seq_comp (f / g) s = seq_div_seq (func_seq_comp f s) (func_seq_comp g s) := rfl,
	rw this,
	apply div_lim_conv,
	from seq_contin.mp ha s hs,
	from seq_contin.mp hb s hs,
	norm_cast, assumption
end

theorem func_comp_func_conv (f g : ℝ → ℝ) (a b c : ℝ) : func_converges_to f a b ∧ func_converges_to g b c → func_converges_to (g ∘ f) a c :=
begin
	repeat {rw seq_contin},
	rintro ⟨ha, hb⟩,
	intros s hs,
	have : func_seq_comp (g ∘ f) s = func_seq_comp g (func_seq_comp f s) := rfl,
	rw this,
	apply hb (func_seq_comp f s),
	from ha s hs
end

end M40002