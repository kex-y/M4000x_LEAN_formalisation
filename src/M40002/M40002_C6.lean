-- M40002 (Analysis I) Chapter 6. Differentiation

import M40002.M40002_C5

namespace M40002

-- Definition of a function being differntiable at a point
def is_derivative (f : ℝ → ℝ) (a l : ℝ) := func_converges_to (λ x : ℝ, (f x - f a) / (x - a)) a l
def differentiable_at (f : ℝ → ℝ) (a : ℝ) := ∃ l : ℝ, is_derivative f a l
def differentiable (f : ℝ → ℝ) := ∀ a : ℝ, differentiable_at f a

-- Differentiable at a point implies continuity at a point
theorem diff_at_to_contin_at (f : ℝ → ℝ) (a : ℝ) : differentiable_at f a → func_continuous_at f a :=
begin
    rw func_continuous_at_to_pos,
    rintros ⟨l, hl⟩ ε hε,
    rcases (hl ε hε) with ⟨δ, ⟨hδ₁, hδ₂⟩⟩,
    let ε' : ℝ := ε / (ε + abs(l)),
    have hε' : 0 < ε' := show 0 < ε / (ε + abs l),
        by {apply (lt_div_iff' _).mpr, linarith,
        from lt_add_of_lt_of_nonneg hε (abs_nonneg l)
        },
    let δ' : ℝ := min δ ε',
    have hδ' : 0 < δ' := show 0 < min δ ε',
        by {rw lt_min_iff, from ⟨hδ₁, hε'⟩},
    use δ', use hδ',
    intros x hx,
    suffices : abs (f x - f a) ≤ abs (f x - f a - (x - a) * l) + abs ((x - a) * l),
    swap, have : abs (f x - f a - (x - a) * l + (x - a) * l) = abs (f x - f a) := by {simp},
    rw ←this,
    apply abs_add,
        apply lt_of_le_of_lt this,
        have hlt : abs (f x - f a - (x - a) * l) < abs (x - a) * ε :=
            by {rw ←div_lt_iff' hx.left,
            rw ←abs_div,
            convert hδ₂ x (lt_of_lt_of_le hx.right (min_le_left δ ε')),
            show (f x - f a - (x - a) * l) / (x - a) = (f x - f a) / (x - a) - l,
            rw sub_div,
            repeat {rw sub_eq_add_neg <|> rw add_left_inj ((f x + -f a) / (x + -a))},
            rw mul_div_cancel_left, from abs_pos_iff.mp hx.left
            },
        apply lt_of_lt_of_le ((add_lt_add_iff_right (abs ((x - a) * l))).mpr hlt),
        rw [abs_mul, tactic.ring_exp.add_overlap_pf (abs (x - a)) rfl],
        apply le_trans (le_of_lt ((mul_lt_mul_right (lt_add_of_lt_of_nonneg hε (abs_nonneg l))).mpr hx.right)),
        have hδle : δ' * (ε + abs l) ≤ (ε / (ε + abs(l))) * (ε + abs l) :=
            by {rw mul_le_mul_right (lt_add_of_lt_of_nonneg hε (abs_nonneg l)), from min_le_right δ ε'},
        apply le_trans hδle,
        rwa [div_eq_mul_inv, mul_assoc, inv_mul_cancel _], linarith,
        suffices : 0 < ε + abs l, linarith,
        from lt_add_of_lt_of_nonneg hε (abs_nonneg l)
end

-- Cor. Differentiable implies continuity
theorem diff_to_contin (f : ℝ → ℝ) : differentiable f → func_continuous f :=
begin
    intros hdiff a,
    apply diff_at_to_contin_at, from hdiff a
end

-- If f and g are both differentiable then so is f + g
theorem diff_sum_diff_func (f g : ℝ → ℝ)  (hf : differentiable f) (hg : differentiable g) : 
differentiable (f + g) :=
begin
    simp,
end

#exit

-- Local and global maximums and minimums
def local_max (f : ℝ → ℝ) (x₀ : ℝ) := ∃ δ > 0, ∀ x ∈ open_interval (x₀ - δ) (x₀ + δ), f x₀ < f x
def local_min (f : ℝ → ℝ) (x₀ : ℝ) := ∃ δ > 0, ∀ x ∈ open_interval (x₀ - δ) (x₀ + δ), f x < f x₀

def global_max (f : ℝ → ℝ) (x₀ : ℝ) := ∀ x : ℝ, f x₀ < f x
def global_min (f : ℝ → ℝ) (x₀ : ℝ) := ∀ x : ℝ, f x < f x₀

theorem global_max_is_local_max {f : ℝ → ℝ} {x₀ : ℝ} : global_max f x₀ → local_max f x₀ :=
begin
    intro hgmax,
    use 1,
    split, norm_num,
    intros x hx,
    from hgmax x
end

theorem global_min_is_local_min {f : ℝ → ℝ} {x₀ : ℝ} : global_min f x₀ → local_min f x₀ := 
begin
    intro hgmix,
    use 1,
    split, norm_num,
    intros x hx,
    from hgmix x
end

-- Fermat's theorem
theorem local_min_diff_zero {f : ℝ → ℝ} {x₀ : ℝ} (h : local_min f x₀) : differentiable_at f x₀ → is_derivative f x₀ 0 :=
begin
    rintro ⟨l, hl⟩,
    rcases h with ⟨δ, hδ₁, hδ₂⟩,
    cases lt_trichotomy l 0,
        {exfalso,
        let ε : ℝ := - l / 2,
        have hε : 0 < ε := show 0 < - l / 2, by linarith,
        rcases hl ε hε with ⟨ω, hω₁, hω₂⟩,
        let μ : ℝ := min δ ω,
        have hμ : 0 < μ :=
            by {show 0 < min δ ω,
            rw lt_min_iff,
            from ⟨hδ₁, hω₁⟩
            },
        let x : ℝ := x₀ + 1 / 2 * μ,
        have h₀ : x ∈ open_interval (x₀ - δ) (x₀ + δ) :=
            by {unfold open_interval, dsimp,
            split,
                {rw add_lt_add_iff_left, suffices : 0 < 2⁻¹ * μ,
                convert lt_trans _ this, norm_num, linarith,
                apply mul_pos', norm_num,
                from hμ
                },
                rw add_lt_add_iff_left, 
                suffices : μ ≤ δ, linarith,
                from min_le_left δ ω
            },
        have h₁ : abs (x - x₀) < ω :=
            by {rw ←abs_lt_open_interval,
            unfold open_interval, dsimp,
            split,
                {rw add_lt_add_iff_left, suffices : 0 < 2⁻¹ * μ,
                convert lt_trans _ this, norm_num, linarith,
                apply mul_pos', norm_num,
                from hμ
                },
                rw add_lt_add_iff_left, 
                suffices : μ ≤ ω, linarith,
                from min_le_right δ ω
            },
        
        --rw abs_lt at hω₂,
        --convert hω₂ x h₁, simp,
        sorry
        },
    sorry
end


end M40002