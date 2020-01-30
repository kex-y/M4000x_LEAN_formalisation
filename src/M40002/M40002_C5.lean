-- M40002 (Analysis I) Chapter 5. Continuity

import M40002.M40002_C4
import data.polynomial

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
lemma seq_contin_conv_lem {s : ℕ → ℝ} {a : ℝ} (h : ∀ n : ℕ, abs (s n - a) < 1 / (n + 1)) : s ⇒ a :=
begin
	intros ε hε,
	cases exists_nat_gt (1 / ε) with N₀ hN₀,
	let N : ℕ := max N₀ 1,
	have hN : 1 / ε < (N : ℝ) :=
		by {apply lt_of_lt_of_le hN₀,
		norm_cast, apply le_max_left
		},
	use N, intros n hn,
	apply lt_trans (h n),
	rw one_div_lt _ hε,
		{apply lt_trans hN,
		norm_cast, linarith},
		{norm_cast, linarith}
end	

theorem lambda_rw (n : ℕ) (f : ℕ → ℝ) : (λ x : ℕ, f x) n = f n := by {rw eq_self_iff_true, trivial}

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
		have hα : ∀ n : ℕ, 1 / ((n : ℝ) + 1) > 0 := 
			by {intro n, simp,
			norm_cast, from nat.zero_lt_one_add n},
		have hβ : ∀ n : ℕ, ∃ (x : ℝ), abs (x - a) < (1 / (n + 1)) ∧ ε ≤ abs (f x - b) := λ n, hδ (1 / (n + 1)) (hα n),
        let s : ℕ → ℝ := λ n : ℕ, classical.some (hβ n),
		have h₀ : s  = λ n : ℕ, classical.some (hβ n) := rfl,
		have hsn : ∀ n : ℕ, abs (s n - a) < 1 / ((n : ℝ) + 1) ∧ ε ≤ abs (func_seq_comp f s n - b) :=
			by {intro n, rw [h₀, lambda_rw n s],
			from classical.some_spec (hβ n)
			},
		have h₁ : s ⇒ a := 
			by {have : ∀ n : ℕ, abs (s n - a) < 1 / ((n : ℝ) + 1) :=
				by {intro n, from (hsn n).left},
			from seq_contin_conv_lem this
			},
        have h₂ : ¬ (func_seq_comp f s ⇒ b) :=
            by {unfold converges_to,
            push_neg, use ε,
            split, from hε,
            intro N, use N,
            split, from nat.le_refl N,
			from (hsn N).right
            },
		exfalso; from h₂ (h s h₁)
        }
end

-- Algebra of limits for functions
def func_add_func (f g : ℝ → ℝ) := λ r : ℝ, f r + g r
instance : has_add (ℝ → ℝ) := ⟨func_add_func⟩


theorem func_add_func_conv (f g : ℝ → ℝ) (a b₁ b₂) : func_converges_to f a b₁ ∧ func_converges_to g a b₂ → func_converges_to (f + g) a (b₁ + b₂) :=
begin
	rintro ⟨ha, hb⟩,
	rw seq_contin,
	intros s hs,
	have : func_seq_comp (f + g) s = seq_add_seq (func_seq_comp f s) (func_seq_comp g s) := rfl,
	rw this,
	apply add_lim_conv,
	from ⟨seq_contin.mp ha s hs, seq_contin.mp hb s hs⟩
end

theorem func_add_func_contin (f g : ℝ → ℝ) : func_continuous f ∧ func_continuous g → func_continuous (f + g) :=
begin
	rintros ⟨ha, hb⟩ a,
	apply func_add_func_conv,
	from ⟨ha a, hb a⟩
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

theorem func_mul_func_contin (f g : ℝ → ℝ) : func_continuous f ∧ func_continuous g → func_continuous (f × g) :=
begin
	rintros ⟨ha, hb⟩ a,
	apply func_mul_func_conv,
	from ⟨ha a, hb a⟩
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

theorem func_comp_func_contin (f g : ℝ → ℝ) : func_continuous f ∧ func_continuous g → func_continuous (g ∘ f) :=
begin
	repeat {unfold func_continuous},
	rintros ⟨ha, hb⟩ a,
	apply func_comp_func_conv,
	swap, from f a,
	from ⟨ha a, hb (f a)⟩
end

-- Starting to prove that all polynomials and rational functions are continuous

lemma constant_contin (c : ℝ) : func_continuous (λ x : ℝ, c) :=
begin
	intros a ε hε,
	simp, use ε,
	from ⟨hε, λ x, λ hx, hε⟩
end

lemma x_contin : func_continuous (λ x : ℝ, x) :=
begin
	intros a ε hε,
	simp, use ε,
	from ⟨hε, λ x, λ hx, hx⟩
end

lemma xn_contin (n : ℕ) : func_continuous (λ x : ℝ, x ^ n) :=
begin
	induction n with k hk,
		{simp, from constant_contin (1 : ℝ)},
		{have : (λ (x : ℝ), x ^ nat.succ k) = func_mul_func (λ x : ℝ, x) (λ x : ℝ, x ^ k) := rfl,
		rw this,
		apply func_mul_func_contin,
		from ⟨x_contin, hk⟩
		}
end

theorem poly_contin {f : polynomial ℝ} : func_continuous (λ x, f.eval x) :=
begin
	apply polynomial.induction_on f,
		{intro a, simp,
		from constant_contin a
		},
		{intros p q hp hq, simp, 
		apply func_add_func_contin (λ x : ℝ, polynomial.eval x p) (λ x : ℝ, polynomial.eval x q),
		from ⟨hp, hq⟩
		},
		simp,
		intros n a hcon,
		apply func_mul_func_contin,
		from ⟨constant_contin a, xn_contin (n + 1)⟩
end

-- Intermediate Value Theorem
theorem intermediate_value {f : ℝ → ℝ} {a b : ℝ} (h₀ : a ≤ b) (h₁ : func_continuous f) : ∀ y : ℝ, f a ≤ y ∧ y ≤ f b → ∃ c : ℝ, a ≤ c ∧ c ≤ b ∧ f c = y :=
begin
	rintros y ⟨hy₁, hy₂⟩,
	cases eq_or_lt_of_le hy₁ with heq hlt₀,
		{use a, split, linarith,
		rw heq, from ⟨h₀, refl y⟩
		},
		{cases eq_or_lt_of_le hy₂ with heq hlt₁,
			{use b, split, linarith,
			rw heq, from ⟨le_refl b, refl (f b)⟩
			},
		clear hy₁ hy₂,
		let S : set ℝ := {d : ℝ | a ≤ d ∧ d ≤ b ∧ f d < y},
		have hbdd : bounded_above S :=
			by {use b, intros s hs, 
			rw set.mem_set_of_eq at hs,
			from hs.right.left
			},
		have hnempty : S ≠ ∅ :=
			by {dsimp, rw set.not_eq_empty_iff_exists,
			use a, rw set.mem_set_of_eq,
			from ⟨le_refl a, h₀, hlt₀⟩
			},
		cases completeness S hbdd hnempty with M hM,
		use M, split,
			apply hM.left a,
			rw set.mem_set_of_eq,
			from ⟨le_refl a, h₀, hlt₀⟩,
		split,
			unfold sup at hM,
			have hα : upper_bound S b :=
				by {intros s hs,
				rw set.mem_set_of_eq at hs,
				from hs.right.left
				},
			cases le_or_lt M b with hβ hγ,
				from hβ,
				exfalso; from (hM.right b hγ) hα,
		rw le_antisymm_iff,
		split,
			{apply classical.by_contradiction,
			push_neg, intro h,
			have : ∃ ε : ℝ, ε = f M - y ∧ 0 < ε :=
				by {use f M - y,
				split, refl,
				linarith
				},
			cases this with ε hε,
			rcases h₁ M ε hε.right with ⟨δ, ⟨hδ, hhδ⟩⟩,
			rw hε.left at hhδ,
			have : ∀ (x : ℝ), abs (x - M) < δ → - (f M - y) < f x - f M ∧ f x - f M < f M - y :=
				by {intros x hx,
				apply abs_lt.mp,
				from hhδ x hx},
			simp at this,
			replace this : ∀ (x : ℝ), abs (x - M) < δ → x ∉ S :=
				by {intros x hx hS,
				rw set.mem_set_of_eq at hS,
				apply asymm (hS.right.right),
				from (this x hx).left
				},
			replace this : upper_bound S (M - δ) :=
				by {intros s hs,
				cases lt_or_le s (M - δ),
					{from le_of_lt h_1},
					{cases lt_or_eq_of_le h_1,
					swap, linarith,
					have hkt : abs (s - M) < δ :=
						by {rw abs_lt,
						split, linarith,
						rw sub_lt_iff_lt_add,
						apply lt_of_le_of_lt (hM.left s hs),
						linarith
						},
					exfalso,
					from (this s hkt) hs
					}
				},
			have hfa : M - δ < M :=
				by {linarith},
			from (hM.right (M - δ) hfa) this
			},

			{have hα : upper_bound S b :=
				by {intros s hs,
				rw set.mem_set_of_eq at hs,
				from hs.right.left
				},
			have hβ : M ≤ b := by {rw ←not_lt, intro hγ, from hM.right b hγ hα},
			cases lt_or_eq_of_le hβ,
			swap, rw h, from le_of_lt hlt₁,

			apply classical.by_contradiction,
			push_neg, intro h,
			have : ∃ ε : ℝ, ε = y - f M ∧ 0 < ε :=
				by {use y - f M,
				split, refl,
				linarith
				},
			cases this with ε hε,
			rcases h₁ M ε hε.right with ⟨δ, ⟨hδ, hhδ⟩⟩,
			rw hε.left at hhδ,
			have : abs (M + (δ / 2) - M) < δ := 
				by {simp,
				rw abs_of_pos (half_pos hδ),
				linarith
				},
			replace this : abs (M + min (δ / 2) ((b - M) / 2) - M) < δ := 
				by {apply lt_of_le_of_lt _ this,
				rw add_comm, simp,
				have hpos : 0 < min (δ / 2) ((b + -M) / 2) :=
					by {simp, split,
					from half_pos hδ,
					linarith
					},
				rw [abs_of_pos hpos, abs_of_pos (half_pos hδ)],
				from min_le_left (δ / 2) ((b - M) / 2),
				},
			replace this : abs (f (M + min (δ / 2) ((b - M) / 2)) - f M) < y - f M :=
				by {from hhδ (M + min (δ / 2) ((b - M) / 2)) this},
			rw abs_lt at this,
			cases this with h₃ h₄,
			simp at h₄,
			have h₅ : M < M + min (δ / 2) ((b + -M) / 2) :=
				by {simp, split,
				from half_pos hδ,
				linarith
				},
			have h₆ : M + min (δ / 2) ((b + -M) / 2) ∈ S :=
				by {rw set.mem_set_of_eq,
				split, apply le_of_lt (lt_of_le_of_lt _ h₅),
				have : a ∈ S := by {rw set.mem_set_of_eq, from ⟨le_refl a, h₀, hlt₀⟩},
				from hM.left a this,
				split,
				cases le_or_lt (δ / 2) ((b + -M) / 2),
					rw min_eq_left h_1,
					suffices : (δ / 2) < b + -M, linarith,
					apply lt_of_le_of_lt h_1, linarith,
					rw min_eq_right (le_of_lt h_1),
					linarith,
					from h₄
				},
			have h₇ : ¬ upper_bound S M :=
				by {unfold upper_bound,
				push_neg, 
				use (M + min (δ / 2) ((b + -M) / 2)),
				from ⟨h₆, h₅⟩
				},
			from h₇ hM.left
			}
		}
end

def func_bounded_above {S : set ℝ} (f : S → ℝ) := bounded_above {t : ℝ | ∀ x : S, t = f x}
def func_bounded_below {S : set ℝ} (f : S → ℝ) := bounded_below {t : ℝ | ∀ x : S, t = f x}

-- TODO Extreme value theorem

def closed_interval (a b : ℝ) := {x : ℝ | a ≤ x ∧ x ≤ b}

lemma mem_of_closed_interval {a b x : ℝ} : x ∈ closed_interval a b ↔ a ≤ x ∧ x ≤ b :=
by {unfold closed_interval, rw set.mem_set_of_eq}

lemma abs_le_closed_interval {x y δ : ℝ} : y ∈ closed_interval (x - δ) (x + δ) ↔ abs (y - x) ≤ δ :=
begin
	unfold closed_interval,
	rw [set.mem_set_of_eq, abs_le],
	split, repeat {rintro ⟨hα, hβ⟩, split, repeat {linarith}}
end

def open_interval (a b : ℝ) := {x : ℝ | a < x ∧ x < b}

lemma mem_of_open_interval {a b x : ℝ} : x ∈ open_interval a b ↔ a < x ∧ x < b := 
by {unfold open_interval, rw set.mem_set_of_eq}

lemma abs_lt_open_interval {x y δ : ℝ} : y ∈ open_interval (x - δ) (x + δ) ↔ abs (y - x) < δ :=
begin
	unfold open_interval,
	rw [set.mem_set_of_eq, abs_lt],
	split, repeat {rintro ⟨hα, hβ⟩, split, repeat {linarith}}
end

-- Defining open and closed sets
def is_open (S : set ℝ) := ∀ x ∈ S, ∃ δ > 0, open_interval (x - δ) (x + δ) ⊆ S
def is_closed (S : set ℝ) := ∀ a : ℕ → ℝ, seq_in a S → (∃ l : ℝ, a ⇒ l) → ∃ l ∈ S, a ⇒ l -- This definition is a bit rubbish...

def is_compact (S : set ℝ) := is_closed S ∧ bounded S

-- An open interval is open

theorem open_interval_is_open (a b : ℝ) : is_open (open_interval a b) :=
begin
	unfold open_interval,
	intros x hx,
	have hδ : 0 < min (x - a) (b - x) :=
		by {apply lt_min_iff.mpr,
		rw set.mem_set_of_eq at hx,
		cases hx with ha hb,
		split, repeat {linarith},
		},
	use min (x - a) (b - x), use hδ,
	unfold open_interval,
	intros y hy,
	rw set.mem_set_of_eq at hy,
	rw set.mem_set_of_eq,
	cases hy with hy₁ hy₂,
	split,
		{apply lt_of_le_of_lt _ hy₁,
		have : min (x - a) (b - x) ≤ x - a := min_le_left (x - a) (b - x),
		linarith
		},
		{apply lt_of_lt_of_le hy₂,
		have : min (x - a) (b - x) ≤ b - x := min_le_right (x - a) (b - x),
		linarith
		}
end

-- A closed interval is closed
theorem closed_interval_is_compact (a b : ℝ) : is_compact (closed_interval a b) :=
begin
	split,
		{unfold is_closed,
		rintros s ha ⟨l, hl⟩,
		use l,
		have h : l ∈ closed_interval a b :=
			by{unfold closed_interval,
			rw set.mem_set_of_eq,
			split,
				{let c : ℕ → ℝ := λ n : ℕ, a,
				have : c ⇒ a := cons_conv,
				apply le_lim c s a l,
				repeat {assumption},
				intro n,
				show a ≤ s n,
				suffices : s n ∈ closed_interval a b,
					unfold closed_interval at this,
					rw set.mem_set_of_eq at this,
					from this.left,
				from ha n
				},
				{let c : ℕ → ℝ := λ n : ℕ, b,
				have : c ⇒ b := cons_conv,
				apply le_lim s c l b,
				repeat {assumption},
				intro n,
				show s n ≤ b,
				suffices : s n ∈ closed_interval a b,
					unfold closed_interval at this,
					rw set.mem_set_of_eq at this,
					from this.right,
				from ha n
				}
			},
		use h, assumption
		},
		{split,
			{use b, intro s,
			unfold closed_interval,
			rw set.mem_set_of_eq,
			intro h, from h.right
			},
			{use a, intro s,
			unfold closed_interval,
			rw set.mem_set_of_eq,
			intro h, from h.left
			}
		}
end

-- The union of open sets is also open
theorem two_union_open_is_open {S T : set ℝ} (h₁ : is_open S) (h₂ : is_open T) : is_open (S ∪ T) :=
begin
	intros x hx,
	rw (set.mem_union x S T) at hx,
	cases hx,
		{rcases (h₁ x hx) with ⟨δ, ⟨hδ₁, hδ₂⟩⟩,
		use δ, use hδ₁,
		intros a ha, left,
		from hδ₂ ha
		},
		{rcases (h₂ x hx) with ⟨δ, ⟨hδ₁, hδ₂⟩⟩,
		use δ, use hδ₁,
		intros a ha, right,
		from hδ₂ ha
		}
end

-- The empty set is open
theorem empty_open : is_open ∅ := 
begin
	intros x hx,
	exfalso, from hx
end

-- The union of a collection of open sets is also open
theorem union_open_is_open {I : Type} {S : I → set ℝ} (h₁ : ∀ i : I, is_open (S i)) : is_open ⋃ i : I, S i :=
begin
	intros x hx,
	rw set.mem_Union at hx,
	cases hx with i hi,
	have h₂ : is_open (S i) := h₁ i,
	unfold is_open at h₂,
	have h₃ : S i ⊆ ⋃ (i : I), S i := set.subset_Union S i,
	rcases h₂ x hi with ⟨δ, ⟨hδ₁, hδ₂⟩⟩,
	use δ, use hδ₁,
	from set.subset.trans hδ₂ h₃
end

lemma element_of_Inter {S : ℕ → set ℝ} {n i : ℕ} : ∀ x ∈ ⋂ i ∈ finset.range n, S i, i ∈ finset.range n → x ∈ S i :=
by {intros x hx hi, rw set.mem_Inter at hx, finish}

-- A function f : ℝ → ℝ is continuous iff. ∀ U ⊆ R, f⁻¹(U) is open
theorem contin_open_pre_image {f : ℝ → ℝ} : func_continuous f ↔ ∀ U : set ℝ, is_open U → is_open {x : ℝ | f x ∈ U} :=
begin
	split,
		{intros h₁ U hU x hx,
		have hf : f x ∈ U := by {rw set.mem_set_of_eq at hx, assumption},
		rcases hU (f x) hf with ⟨ε, ⟨hε, hrang⟩⟩,
		rcases h₁ x ε hε with ⟨δ, ⟨hδ, hcontin⟩⟩,
		use δ, use hδ,
		intros y hy,
		rw set.mem_set_of_eq,
		rw abs_lt_open_interval at hy,
		suffices : f y ∈ open_interval (f x - ε) (f x + ε),
			from hrang this,
		rw abs_lt_open_interval,
		from hcontin y hy
		},
		{intros hU y ε hε,
		let U : set ℝ := open_interval (f y - ε) (f y + ε),
		have : f y ∈ U := by {rw abs_lt_open_interval, simpa},
		rcases hU U (open_interval_is_open (f y - ε) (f y + ε)) y this with ⟨δ, ⟨hδ, hrang⟩⟩,
		use δ, use hδ,
		intros x hx,
		rw ←abs_lt_open_interval at hx,
		rw ←abs_lt_open_interval,
		suffices : x ∈ {x : ℝ | f x ∈ U},
			rw set.mem_set_of_eq at this,
			assumption,
		from hrang hx
		}
end

-- a n → l iff ∀ U ⊆ ℝ, U an open set, l ∈ U ⇒ ∃ N ∈ ℕ, ∀ n ≥ N, a n ∈ U (Unseen 2 Term 2)
lemma seq_converge_imples_all_open {a : ℕ → ℝ} {l : ℝ} : a ⇒ l → ∀ U : set ℝ, is_open U ∧ l ∈ U → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (a n) ∈ U :=
begin
	rintros hconv U ⟨hU, hlU⟩,
	rcases hU l hlU with ⟨δ, ⟨hδ₁, hδ₂⟩⟩,
	cases hconv δ hδ₁ with N hN,
	use N, intros n hn,
	suffices : a n ∈ open_interval (l - δ) (l + δ),
		from hδ₂ this,
	rw abs_lt_open_interval,
	from hN n hn
end

lemma all_open_imples_seq_converge {a : ℕ → ℝ} {l : ℝ} : (∀ U : set ℝ, is_open U ∧ l ∈ U → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (a n) ∈ U) → a ⇒ l :=
begin
	intros hU ε hε,
	let U : set ℝ := open_interval (l - ε) (l + ε),
	have hopen : is_open U :=
		by {apply open_interval_is_open},
	have hlU : l ∈ open_interval (l - ε) (l + ε) :=
		by {unfold open_interval,
			rw set.mem_set_of_eq,
			split, all_goals {linarith},
		},
	cases hU U ⟨hopen, hlU⟩ with N hN,
	use N, intros n hn,
	rw ←abs_lt_open_interval,
	from hN n hn
end

theorem seq_converge_iff_all_open {a : ℕ → ℝ} {l : ℝ} : a ⇒ l ↔ ∀ U : set ℝ, is_open U ∧ l ∈ U → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (a n) ∈ U :=
by {split, all_goals {try {from seq_converge_imples_all_open <|> from all_open_imples_seq_converge}}}

-- Uniform continuity and convergence
def unif_contin (f : ℝ → ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, abs (x - y) < δ → abs (f x - f y) < ε

-- Uniformly continuous implies continuous (hence is stronger)
theorem unif_contin_implies_contin {f : ℝ → ℝ} : unif_contin f → func_continuous f :=
begin
	intros h₁ a ε hε,
	rcases h₁ ε hε with ⟨δ, ⟨hδ₁, hδ₂⟩⟩,
	use δ, use hδ₁, intro x,
	from hδ₂ x a
end

def func_pointwise_converge_to (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) := ∀ x : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → abs (f n x - g x) < ε
def func_converge_uniform (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) := ∀ ε > 0, ∃ N : ℕ, ∀ x : ℝ, ∀ n : ℕ, N ≤ n → abs (f n x - g x) < ε

-- function.swap swaps 
-- f: ℕ → ℝ → ℝ = fₙ(x)

-- If a sequence of uniformly continuous functions f n converges to f, then f is uniformly continuous
theorem unif_contin_lim_unif_contin (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (h : ∀ n : ℕ, unif_contin (f n)) : func_converge_uniform f g → unif_contin g :=
begin
	intros h₁ ε hε,
	have  hε₂: 0 < ε / 3 := by linarith,
	cases h₁ (ε / 3) hε₂ with N hN,
	rcases h N (ε / 3) hε₂ with ⟨δ, ⟨hδ₁, hδ₂⟩⟩,
	use δ, use hδ₁, 
	intros x y hxy,
	suffices : abs (g x -f N x) + abs (f N x - f N y) + abs (f N y - g y) < ε,
		{apply lt_of_le_of_lt _ this,
		 convert le_trans (abs_add (g x - f N y) (f N y - g y)) _, simp,
		 apply add_le_add_right',
		 convert abs_add (g x - f N x) (f N x - f N y),
		 simp
		},
	have : ε = ε / 3 + ε / 3 + ε / 3 := by {linarith},
	rw this,
	repeat {apply add_lt_add},
		{rw abs_sub,
		from hN x N (le_refl N)},
		{from hδ₂ x y hxy},
		{from hN y N (le_refl N)}
end

end M40002