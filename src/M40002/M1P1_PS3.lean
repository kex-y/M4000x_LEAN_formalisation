-- M1P1 Problem Sheet 3

import M40002.M40002_C3

namespace M40002

-- Q1. Suppose that (an) and (bn) are sequences of real numbers such that an ≤ bn ∀n and an → a, bn → b. Prove that a ≤ b.
/-
This question is answered by le_lim
-/
#check le_lim

-- Q2. Suppose that an ≤ bn ≤ cn ∀n and that an → a and cn → a. Prove that bn → a.
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



end M40002
