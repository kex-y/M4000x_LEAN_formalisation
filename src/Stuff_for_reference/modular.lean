import tactic.ring

def mod (a b n : ℤ) := ∃ k : ℤ, (a - b) = k * n

example
    (a b n : ℤ) : mod a b n → ∃ k : ℤ, (a - b) = k * n :=
begin
  intro h,
  exact h,
end

theorem modsymm
    (a b n : ℤ) : mod a b n ↔ mod b a n :=
begin
    split,
    intro h,
        cases h with x hx,
        existsi -x,
        ring,
        rw ←hx,
        ring,
    intro h,
        cases h with x hx,
        existsi -x,
        ring,
        rw ←hx,
        ring,
end

theorem modrefl
    (n : ℤ) : ∀ a : ℤ, mod a a n :=
begin
    intro x,
    have h : ∃ k : ℤ, x - x = k * n,
        ring, use 0, ring,
-- Note : Using fapply exists.intro also works.
    assumption,
end

theorem modtrans
    (a b c n : ℤ) : mod a b n ∧ mod b c n → mod a c n :=
begin
    intro h,
    cases h with hab hbc,
    cases hab with x hx,
    cases hbc with y hy,
    existsi x + y,
    rw add_mul,
    rw ←hx, rw ←hy,
    ring,
end

-- Hence mod is an equivalence relation!

theorem modadd
    (a b c n : ℤ) : mod a b n → mod (a + c) (b + c) n :=
begin
    intro h,
    cases h with x hx,
    existsi x,
    ring, rw hx, ring,
end

theorem modmul
    (a b c n : ℤ) : mod a b n → mod (a * c) (b * c) n :=
begin
    intro h,
    cases h with x hx,
    existsi c * x,
    rw mul_assoc,
    rw ←hx, ring,
end

-- Introducing greatest common divisors!

def div (a b : ℤ) := ∃ k : ℤ, k * a = b
    -- or use ∣ (\mid)

-- I would like to define gcd as the largest common divisor
def S (a b : ℤ) := {x : ℕ | div x a ∧ div x b}
-- def gcd (a b : ℤ) := max (S a b)

/- def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (y % succ x) (succ x) -/

namespace nat

-- Show gcd a b = d has the properties (div d a ∧ div d b) ∧ (∀ c : ℤ, div c a ∧ div c b → div c d)

theorem gcdzero : ∀ c : ℕ, gcd 0 c = c :=
begin
    intro x,
    unfold gcd,
end

-- #print notation %

theorem gcdsym (a b : ℕ) : gcd a b = gcd b a :=
begin
    /- cases b with h0 hx,

    have ha : gcd 0 a = a, unfold gcd,
    have hb : gcd a 0 = a,
        induction a with hi hy,
        refl, unfold gcd, refl,
    rw ha, rw hb,-/
    
    induction a with x hx,
    unfold gcd,
    induction b with b hb,
    unfold gcd, unfold gcd, refl,

    induction b with b hb,
    unfold gcd, refl,
    unfold gcd, 
        
    sorry,


end

theorem gcdp1
    (a b : ℕ) (d : ℕ) : (gcd a b = d) → (d ∣ a ∧ d ∣ b) :=
begin
    intro h,
    split,

    cases d, 
    existsi 0, ring,
    have h0 : ∀ a b : ℕ, gcd a b = 0 → a = 0 ∧ b = 0,
    intros ha hb, contrapose, push_neg,

 
end

theorem gcdp1
    (a b : ℕ) (d : ℕ) : (gcd a b = d) → (∀ c : ℤ, c ∣ a ∧ c ∣ b → c ∣ d) :=
begin
 
end

theorem gcdp
    (a b : ℕ) (d : ℕ) : (gcd a b = d) ↔ (d ∣ a ∧ d ∣ b) ∧ (∀ c : ℤ, c ∣ a ∧ c ∣ b → c ∣ d) :=
begin
 
end

example : gcd 5 10 = 5 :=
begin
    have ha : ∀ c : ℤ, div c 5 ∧ div c 10 → div c 5,
        intros x hx,
        exact hx.left,
    have hb : div 5 5 ∧ div 5 10,
        split, 
        use 1, refl,
        use 2, refl,


end
