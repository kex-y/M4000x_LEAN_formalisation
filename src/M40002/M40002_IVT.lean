-- Intermediate Value Theorem

import M40002.M40002_C5

namespace M40002

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

end M40002
