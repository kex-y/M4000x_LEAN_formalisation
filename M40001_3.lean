-- begin header
import tactic.ring
import data.real.basic
import data.setoid
import tactic.linarith
import tactic.norm_cast

namespace M40001_3
-- end header

/-Section
2.5 Binary Relations
-/

variables {X Ω : Type}
def bin_rel (R : Type) := X → X → Prop

/- Section 
2.6 Common Predicates on Binary Relations
-/

def reflexive (r : setoid X) := ∀ x : X, r.rel x x

/- Theorem
$≤$ is reflexive.
-/
theorem le_refl : ∀ x : ℝ, x ≤ x := by {intro; refl}

def symmetric (r : setoid X) := ∀ x y : X, r.rel x y → r.rel y x

/- Theorem
$=$ is symmetric.
-/
theorem eq_symm : ∀ x y : ℝ, x = y → y = x :=
by {intros x y h, rwa h}

def antisymmetric (r : setoid X) := ∀ x y : X, r.rel x y ∧ r.rel y x → x = y

/- Theorem
$≤$ is anti-symmetric.
-/
theorem le_antisymm : ∀ x y : ℝ, x ≤ y ∧ y ≤ x → x = y :=
begin
-- Suppose we have $x, y ∈ ℝ$ where $x ≤ y$ and $y ≤ x$, then we need to show that $x = y$.
    intros x y h,
    have h0 : (x < y ∨ x = y) ∧ (y < x ∨ y = x),
        repeat {rw ←le_iff_lt_or_eq}, assumption,
-- By the trichotomy axioms, either $x < y$, $y < x$ or $x = y$.
    cases lt_trichotomy x y with ha hb,
-- Let's first suppose that $x < y$, then obviously $¬ (y < x)$. But since we have $y ≤ x$, $x$ must therefore equal to $y$!
    {suffices : ¬ (y < x),
        cases h0.right with hc hd, contradiction, rwa hd,
    simp, from h.left},
    {cases hb with he hf,
-- Let's now consider the other two cases. If $x = y$ then there is nothing left to prove so lets suppose $y < x$.
    {assumption},
-- Similar to before, $(y < x) ⇒ ¬ (x < y)$. But $(x ≤ y)$, therefore $x = y$!
    {suffices : ¬ (x < y),
        cases h0.left with hc hd, contradiction, rwa hd,
    simp, from h.right}
    }
end

def transitive (r : setoid X ) := ∀ x y z : X, r.rel x y ∧ r.rel y z → r.rel x z

/- Theorem
$⇒$ is transitive.
-/
theorem imply_trans (P Q R : Prop) : (P → Q) ∧ (Q → R) → P → R :=
by {intros h p, from h.right (h.left p)}

/- Theorem
$≤$ is also transitive.
-/
theorem le_trans : ∀ x y z : ℝ, (x ≤ y) ∧ (y ≤ z) → x ≤ z :=
by {intros x y z h, from le_trans h.left h.right}

/- Section
2.7 Partial and Total Orders
-/

def partial_order (r : setoid X) := reflexive r ∧ symmetric r ∧ transitive r
def total (r : setoid X) := ∀ x y, r.rel x y ∨ r.rel y x
def total_order (r : setoid X) := partial_order r ∧ total r

/- Theorem
$≤$ is a total order.
-/
-- As we already have already proven that $≤$ is reflexive, symmetric, and transitive, i.e. its a partial order, we only need to show $≤$ is total to prove that $≤$ is a total order.
/- Lemma
$≤$ is total.
-/
theorem le_total : ∀ x y : ℝ, x ≤ y ∨ y ≤ x :=
begin
-- Suppose we have $x, y ∈ ℝ$, by the trichotomy axiom, either $x < y$, $y < x$ or $x = y$.
    intros x y,
    repeat {rw le_iff_lt_or_eq},
    cases lt_trichotomy x y,
-- If $x < y$ then $x ≤ y$.
    {left, left, assumption},
-- If $x = y$ then also $x ≤ y$. However, if $y > x$, then we have $y ≤ x$. Thus, by considering all the cases, we see either $x ≤ y$ or $y ≤ x$. 
    {cases h, repeat { {left, assumption} <|> right <|> assumption }, rwa h}
end

/- Section
2.7 Equivalence Relations
-/

def equivalence (r : setoid X) := reflexive r ∧ symmetric r ∧ transitive r

/- Sub-section
Examples
-/

/-
Example 2. Suppose we define a binary relation $R(m, n)$, $m, n ∈ ℤ$, where $R(m, n)$ is true if and only if $m - n$ is even.
-/

def R (m n : ℤ) := 2 ∣ (m - n)

/- Lemma
(1) $R$ is reflexive.
-/
theorem R_refl : ∀ m : ℤ, R m m :=
begin
-- We have for any $m ∈ ℝ$, $m - m = 0$.
    intro,
    unfold R, 
-- As $2 ∣ 0$, we have $R(m, m)$ is true!
    simp,
end

/- Lemma
(2) $R$ is symmetric.
-/
theorem R_symm : ∀ m n : ℤ, R m n → R n m :=
begin
-- Suppose we have $m, n ∈ ℝ$ such that $R(m, n)$ is true.
    intros m n,
-- As $R(m, n)$ implies $2 ∣ m - n$, $∃ x ∈ ℤ, 2 x = m - n$.
    rintro ⟨x, hx⟩,
    existsi -x,
-- But this means $2 (-x) = n - m$, i.e. $2 ∣ n - m$, thus $R(n, m)$ is also true!
    simp, rw ←hx, ring,
end

/- Lemma
(3) $R$ is transitive.
-/
theorem R_trans : ∀ l m n : ℤ, (R m l) ∧ (R l n) → R m n :=
begin
-- Suppose we have $l, m, n ∈ ℝ$ such that $R(m, l)$ and $R(l, n)$, we need to show $R(m, n)$ is true.
    intros l m n,
-- Since $R(m, l)$ and $R(l, n)$ implies $2 ∣ m - l$ and $2 ∣ l - n$, $∃ x, y ∈ ℤ, 2 x = m - l, 2 y = l - n$.
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩,
    existsi x + y,
-- But then $2 (x + y) = 2 x + 2 y = m - l + l - n = m - n$. Thus $2 ∣ m - n$, i.e. $R(m, n)$.
    ring, rw [←hx, ←hy], ring,
end

/- Theorem
$R$ is an equivalence relation.
-/
-- This follows directly from lemma (1), (2), and (3).

/-
Example 4. 
-/

def brel (A B : set Ω) : ∃ g : A → B, function.bijective g

/- Theorem
$~$ is reflexive.
-/
theorem brel_refl (A : set Ω) : brel A A :=

/-
Example 5.
-/

end M40001_3