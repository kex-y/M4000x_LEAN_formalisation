-- begin header
import tactic.ring
import data.rat.basic
import data.rat.cast
import tactic.linarith
import tactic.library_search
import tactic.norm_cast

namespace M40001
-- end header

/- Section
1.3 Relations
-/

/- Sub-section 
1.3.1 The Law of the Excluded Middle
-/

-- Scrapted
/- Theorem
The law of the excluded middle states that if $P$ is a proposition, then $ ¬ (¬ P) ⇔ P$.
-/
theorem excluded_mid
    (P : Prop) : ¬ (¬ P) ↔ P :=
begin
    -- We need to show that $¬ (¬ P)$ is true if and only if $P$ is true. So we consider both directions of the implication.
    split,
    -- We now need to show that $¬ (¬ P)$ is true implies that $P$ is also true, so let's suppose that $¬ (¬ P)$ is true.
    intro hp,
    -- Suppose we now make a dubious assumption that $¬ P$ is true.
    apply classical.by_contradiction,
    intro hnp,
    -- But $¬ P$ is true implies that $¬ (¬ P)$ is false which is a contradiction to our premis that $¬ (¬ P)$ is true, so $¬ P$ must be false, resulting in the first part of the proof!
    exact hp hnp,
    -- Now we need to proof that the backwards implication is also correct, i.e. $P$ is true implies $¬ (¬ P)$ is also true.
    -- To show that $¬ (¬ P)$ is true when $P$ is true, we can simply show that $P$ is true implies $¬ P$ is false.
    intros hp hnp,
    exact hnp hp,
    -- But this is true by definition, so we have nothing left to prove!
end

/- Sub-section
1.3.2 De Morgan's Laws
-/

/- Theorem
(1) Let $P$ and $Q$ be propositions, then $¬ (P ∨ Q) ⇔ (¬ P) ∧ (¬ Q)$
-/
theorem demorgan_a
    (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬ P) ∧ (¬ Q) :=
begin
    -- Again we have an 'if and only if' statement so we need to consider both directions of the argument.
    split,
    -- We first show that $¬ (P ∨ Q) ⇒ ¬ P ∧ ¬ Q$ through contradiction. Suppose $¬ (P ∨ Q)$ is true, and we make a dubious assumption that $P$ is true.
    intro h,
    split,
    intro hp,
    -- But then $¬ (P ∨ Q)$ is false! A contradiction! Therefore $P$ must be false.
    apply h,
    left, exact hp,
    -- Similarly, supposing $Q$ is true also results in a contradiction! Therefore $Q$ is also false. 
    intro hq,
    apply h,
    right, exact hq,
    -- With that, we now focus our attention on the backwards implication, i.e. $(¬ P) ∧ (¬ Q) ⇒ ¬ (P ∨ Q)$.
    -- Again, let's approach this by contradiction. Given $¬ P ∧ ¬ Q$ suppose we have $P$ or $Q$.
    intros h hpq,
    -- But $P$ can't be true, as we have $¬ P$,
    cases hpq with hp hq,
    cases h with hnp hnq,
    exact hnp hp, 
    -- So since, we assumed $P$ or $Q$, then $Q$ must be true.
    -- But $Q$ also can't be true as we have $¬ Q$!
    cases h with hnp hnq,
    exact hnq hq,
    -- Therefore, given $(¬ P) ∧ (¬ Q)$, $(P ∨ Q)$ must not be true, i.e. $¬ (P ∨ Q)$ is true, which is exactly what we need!
end

/- Theorem
(2) Let $P$ and $Q$ be propositions, then $¬ (P ∧ Q) ⇔ (¬ P) ∨ (¬ Q)$
-/
theorem demorgan_b
    (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P) ∨ (¬ Q) :=
begin
    -- Once again, we have an if and only if statement, therefore, we need to consider both directions. 
    split,
    -- We first show that $¬ (P ∧ Q) ⇒ ¬ P ∨ ¬ Q$. Suppose $¬ (P ∧ Q)$.
    intro h,
    -- By the law of the excluded middle, we have either $P$ or $¬ P$.
    cases (classical.em P) with hp hnp,
    -- Suppose first that we have $P$. Then, we must have $¬ Q$ as having $Q$ implies $P ∧ Q$ which contradicts with $¬ (P ∧ Q)$,
    have hnq : ¬ Q,
        intro hq,
        have hpq : P ∧ Q,
            split, exact hp, exact hq,
        exact h hpq,
    -- hence, we have $¬ P ∨ ¬ Q$.
    right, exact hnq,
    -- Now let's suppose $¬ P$. But as $¬ P$ implies $¬ P ∨ ¬ Q$, we have nothing left to prove.
    left, exact hnp,
    -- With the forward implication dealt with, let's consider the reverse, i.e. $¬ P ∨ ¬ Q ⇒ ¬ (P ∧ Q)$.
    -- Given $¬ P ∨ ¬ Q$ let's suppose that $P ∧ Q$.
    intros h hpq,
    -- But this is a contradiction as $P ∧ Q$ implies that neither $P$ nor $Q$ is false!
    cases h with hnp hnq,
        cases hpq with hp hq,
        exact hnp hp,
        cases hpq with hp hq,
        exact hnq hq,
    -- Therefore, $P ∧ Q$ must be false by contradiction.
end

/- Sub-section
1.3.3 Transitivity of Implications, and the Contrapositive
-/

/- Theorem
$⇒$ is transitive, i.e. if $P$, $Q$, and $R$ are propositions, then $P ⇒ Q$ and $Q ⇒ R$ means $P ⇒ R$.
-/
theorem imp_trans
    (P Q R : Prop) : (P → Q) ∧ (Q → R) → (P → R) :=
begin
    -- Suppose $P ⇒ Q$ and $Q ⇒ R$ are both true, we then would like to prove that $P ⇒ R$ is true.
    intro h,
    cases h with hpq hqr,
    -- Say that $P$ is true,
    intro hp,
    -- then by $P ⇒ Q$, $Q$ must be true. But we also have $Q ⇒ R$, therefore $R$ is also true, which is exactly what we wish to prove!
    exact hqr (hpq hp),
end

/- Theorem
If $P$ and $Q$ are propositions, then $(P ⇒ Q) ⇔ (¬ Q ⇒ ¬ P)$.
-/
theorem contra
    (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
    -- Let's first consider the implication from left to right, i.e. $(P ⇒ Q) ⇒ (¬ Q ⇒ ¬ P)$.
    split,
    -- We will prove this by contradiction, so suppose we have $P ⇒ Q$, $¬ Q$ and not $¬ P$. 
    intros h hnq hp,
    -- But not $¬ P$ is simply $P$, and $P$ implies $Q$, a contradiction to $¬ Q$! Therefore, $P ⇒ Q$ must imply $¬ Q ⇒ ¬ P$ as required.
    exact hnq (h hp),
    -- Now lets consider reverse, $(¬ Q ⇒ ¬ P) ⇒ (P ⇒ Q)$. Suppose we have $¬ Q ⇒ ¬ P$ and $P$.
    intros h hp,
    -- If $Q$ is true then we have nothing left to prove, so suppose $¬ Q$ is true.
    cases (classical.em Q) with hq hnq,
    exact hq,
    exfalso,
    -- But $¬ Q$ implies $¬ P$ which contradicts with $P$, therefore, $¬ Q$ must be false as requied.
    exact h hnq hp,
end

/- Sub-section
1.3.4 Distributivity
-/

/- Theorem
(1) If $P$, $Q$, and $R$ are propositions. Then, $P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)$;
-/
theorem dis_and_or
    (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
    -- Let's first consider the foward implication, $P ∧ (Q ∨ R) ⇒ (P ∧ Q) ∨ (P ∧ R)$
    split,
    -- Suppose we have $P ∧ (Q ∨ R)$,
    intro h,
    -- then $P$ is true and either $Q$ or $R$ is true.
    cases h with hp hqr,
    -- But this means either $P$ and $Q$ is true or $P$ and $R$ is true which is exactly what we need.
    cases hqr with hq hr,
    left, split, repeat {assumption},
    right, split, repeat {assumption},
    -- With that, we now need to prove the backwards implication. Suppose $(P ∧ Q) ∨ (P ∧ R)$.
    intro h,
    -- Let's consider both cases.
    cases h with hpq hpr,
    -- If $P ∧ Q$ is true, then $P$ is true and $Q ∨ R$ is also true.
    cases hpq with hp hq,
    split, assumption, left, assumption,
    -- Similarly, is $P ∧ R$ is true, then $P$ is true and $Q ∨ R$ is also true. 
    cases hpr with hp hr,
    split, assumption, right, assumption,
    -- Therefore, by considering bothe cases, we see that either $P ∧ Q$ or $P ∧ R$ implies $P ∧ (Q ∨ R)$.
end

/- Theorem
(2) $P ∨ (Q ∧ R) ⇔ (P ∨ Q) ∧ (P ∨ R)$.
-/
theorem dis_or_and
    (P Q R : Prop) : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
begin
    -- We first consider the forward implication $P ∨ (Q ∧ R) ⇒ (P ∨ Q) ∧ (P ∨ R)$.
    split,
    -- Suppose we have $P ∨ (Q ∧ R)$, then either $P$ is true or $Q$ and $R$ is true$.
    intro h,
    -- Let's consider both cases. If $P$ is true, then both $P ∨ Q$ and $P ∨ R$ are true.
    cases h with hp hqr,
    split, repeat {left, assumption},
    -- Similarly, if $P$ and $Q$ are true, then both $P ∨ Q$ and $P ∨ R$ are true. 
    cases hqr with hq hr,
    split, repeat {right, assumption},
    -- Now let's consider the backwards implication. Suppose that $(P ∨ Q)$ and $(P ∨ R)$ is true and lets consider all the cases.
    intro h,
    cases h with hpq hpr,
    -- If $P$ is true the $P ∨ (Q ∧ R)$ is also true.
    cases hpq with hp hq,
    cases hpr with hp hr,
    repeat {left, assumption},
    -- If $¬ P$ is true then from $(P ∨ Q)$ and $(P ∨ R)$, $Q$ and $R$ must be true, and therefore, $P ∨ (Q ∧ R)$ is also true.
    cases hpr with hp hr,
    left, assumption,
    right, split, repeat {assumption},
end

/- Section
1.4 An Application
-/

/- 
We would like prove that there is no rational number whose square is 2 using the techniques introduced earlier.
-/

def even (a : ℤ) := ∃ b : ℤ, a = 2 * b
def odd (a : ℤ) := ∃ b : ℤ, a = 2 * b + 1
set_option trace.check true

lemma not_even_is_odd (n : ℤ) : ¬ even n ↔ odd n := 
begin
    split,
    intro ha,
    have hb : n % 2 = 1,
        have hc : n % 2 = 0 ∨ n % 2 = 1,
            apply int.mod_two_eq_zero_or_one,
        cases hc with hx hy,
        exfalso,
        apply ha,
        existsi n / 2,
        rw int.mul_div_cancel_of_mod_eq_zero hx,
        assumption,
    have hc : (n - 1) % 2 = 0,
    have hd : n % 2 = 1 % 2, rw hb, refl,
        revert hd,
        rw int.mod_eq_mod_iff_mod_sub_eq_zero,
        intro h, assumption,
    existsi (n - 1) / 2,
    rw int.mul_div_cancel_of_mod_eq_zero hc,
    simp,

    intro ha,
    intro hb,
    cases ha with x hx,
    cases hb with y hy,
    have hc : n % 2 = 1,
        rw hx, simp, refl,
    have hd : n % 2 = 0,
        rw hy, simp,
    have he : (1 : ℤ) = (0 : ℤ),
        rwa [←hc, ←hd],
    have hf : ¬ ( (1 : ℤ) = (0 : ℤ)), simp,
    exact hf he,
end
lemma gcdeven (n m : ℕ) : 2 ∣ nat.gcd (2 * n) (2 * m) :=
begin
    have ha : 2 ∣ 2 * n, existsi n, refl,
    have hb : 2 ∣ 2 * m, existsi m, refl,
    have hc : (2 ∣ 2 * n) → (2 ∣ 2 * m) → 2 ∣ nat.gcd (2 * n) (2 * m),
    exact nat.dvd_gcd,
    apply hc,
    repeat {assumption},
end

/- Theorem
If $a$ is an integer, then $a$ is even is and only if $a^2$ is even.
-/
lemma times_even
  (a : ℤ) : even a ↔ even (a ^ 2) :=
begin
    split,
    intro h,
    have ha : ∃ b : ℤ, a = 2 * b, exact h,
    have hb : ∃ b : ℤ, a ^ 2 = 2 * b,
        cases ha with x hx,
        existsi 2 * x ^ 2,
        rw hx,
        ring,
    exact hb,

    intro h,
    apply classical.by_contradiction,
    intro ha,
    have hc : odd a,
        rw ←not_even_is_odd a,
        assumption,
    have hd : odd (a ^ 2),
        cases hc with x hx,
        existsi 2 * x ^ 2 + 2 * x,
        rw hx,
        ring,
    have he : ¬ even (a ^ 2),
        rw not_even_is_odd (a ^ 2),
        assumption,
    exact he h,
end

/- Theorem
There is no rational number whose square is 2.
-/
--set_option pp.all true
theorem rational_not_sqrt_two : ¬ ∃ r : ℚ, r ^ 2 = 2  := 
begin
    -- First show that p is even
    push_neg,
    intro r,
    -- Manipulate the fraction to have the properties desired
    have h : rat.mk (r.num) (r.denom) = r,
        apply rat.num_denom,
    rw ←h,
    intro hcon,
    -- The denominator must not be zero
    have hdnot0 : r.denom ≠ 0,
        intro ha,
        have hb : rat.mk (r.num) (r.denom) ^ 2 = 0,
            rw ha,
            refl,
        convert hb,
        rw hcon,
        simp,
        linarith,
    -- The numerator must also not be zero
    have hnnot0 : r.num ≠ 0,
        intro ha,
            have hb : rat.mk (r.num) (r.denom) ^ 2 = 0,
                rw ha,
                simp, refl,
            convert hb,
            rw hcon,
            simp,
            linarith,
    -- The fraction is in its lowest terms
    have hcop : nat.coprime (int.nat_abs r.num) r.denom,
        cases r with ha hb hc hd,
        exact hd,
    -- Now we can begin the actual proof...
    -- First show that r.num ^ 2 is even
    have hsqrneven : even (r.num ^ 2),
        existsi (r.denom : ℤ) ^ 2,
        have ha : r.num ^ 2 = r.num ^ 2 * 1,
            simp,
        rwa [ha, ←rat.mk_eq],
        convert hcon,
        repeat {rw pow_two},
        rw rat.mul_def,
        all_goals {try {simp, apply hdnot0,}},
        simp,
    -- Now we can use times_even to show r.num is even
    have hneven : even r.num, rw times_even, assumption,
    -- r.num is even → r.denom ^ 2 is also even
    have hsqrdeven : even (r.denom ^ 2),
        cases hneven with b ha,
        existsi b ^ 2,
        have hb : (2 * ↑(r.denom) ^ 2 = 4 * (b ^ 2)) → (↑(r.denom) ^ 2 = 2 * b ^ 2),
            have hβ : 4 * b ^ 2 = 2 * 2 * b ^ 2, refl,
            rwa [hβ, ←sub_eq_zero],
            have hγ : 2 * ↑(r.denom) ^ 2 - 2 * 2 * b ^ 2 = 2 * (↑(r.denom) ^ 2 - 2 * b ^ 2), ring,
            rwa [hγ, mul_eq_zero],
            intro hδ,
            cases hδ with hδ1 hδ2,
            exfalso,
            convert hδ1, simp, linarith,
            rw ←sub_eq_zero,
            assumption,
        rw hb,
        have hc : 4 * b ^ 2 = (2 * b) ^ 2,
            ring,
        rwa [hc, ←ha],
    have hd : ↑r.denom * ↑r.denom = r.denom * r.denom, simp,
        have he : rat.mk (r.num ^ 2) (r.denom ^ 2) = 2, 
            rw ←hcon, 
            repeat {rw pow_two}, 
            rw rat.mul_def,
            repeat {simp, apply hdnot0,},
        have hf : rat.mk r.num r.denom = r.num / r.denom, 
            exact rat.mk_eq_div (r.num) ↑(r.denom),
        have hg : 2 * (↑(r.denom) ^ 2) =  r.num ^ 2 * 1 → 2 * (↑(r.denom) * ↑(r.denom)) = r.num * r.num,
            repeat {rw pow_two},
            rw mul_one,
            intro hh,
            assumption,
        rw hg,
        rw ←rat.mk_eq,
        rw he,
        refl,
        simp,
        rw pow_two,
        intro hh,
        have hi : r.denom = 0,
            have hj : r.denom * r.denom = 0,
                rw ←hd,
                exact_mod_cast hh,
            rw nat.mul_eq_zero at hj,
            revert hj,
            simp,
        exfalso,
        exact hdnot0 hi,
    have hdeven : even r.denom, rw times_even, assumption,
    -- But that means r.num and r.denom are not coprimes
    have hncop : ¬ nat.coprime (int.nat_abs (r.num)) (r.denom),
        have ha : ¬ nat.coprime (int.nat_abs (r.num)) (r.denom) ↔ nat.gcd (int.nat_abs (r.num)) (r.denom) ≠ 1, refl,
        rw ha,
        cases hneven with k hk,
        cases hdeven with m hm,
        rw hk,
        have hb : int.nat_abs r.denom = 2 * (int.nat_abs m),
            rwa [hm, int.nat_abs_mul],
            refl,
        have hc : (r.denom : ℕ) = int.nat_abs r.denom, refl,
        rwa [hc, hb],
        have hd : int.nat_abs (2 * k) = 2 * int.nat_abs k, rw int.nat_abs_mul, refl,
        rw hd,
        intro he,
        have hf : ¬ (2 ∣ nat.gcd (2 * int.nat_abs k) (2 * int.nat_abs m)),
            rw he,
            simp,
            linarith,
        have hg : 2 ∣ nat.gcd (2 * int.nat_abs k) (2 * int.nat_abs m),
            apply gcdeven,
        exact hf hg,
    exact hncop hcop,
end

end M40001
