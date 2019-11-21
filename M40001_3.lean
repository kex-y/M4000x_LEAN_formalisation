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
universe u
variables {X V : Type u}
def bin_rel (R : Type*) := X → X → Prop

/- Section 
2.6 Common Predicates on Binary Relations
-/

def reflexive (r : bin_rel X) := ∀ x : X, r x x

/- Theorem
$≤$ is reflexive.
-/
@[simp] theorem le_refl : reflexive ((≤) : ℝ → ℝ → Prop) := by {intro; refl}

def symmetric (r : bin_rel X) := ∀ x y : X, r x y → r y x

/- Theorem
$=$ is symmetric.
-/
theorem eq_symm : symmetric ((=) : ℝ → ℝ → Prop) :=
by {intros x y h, rwa h}

def antisymmetric (r : bin_rel X) := ∀ x y : X, r x y ∧ r y x → x = y

/- Theorem
$≤$ is anti-symmetric.
-/
@[simp] theorem le_antisymm : antisymmetric ((≤) : ℝ → ℝ → Prop) :=
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

def transitive (r : bin_rel X) := ∀ x y z : X, r x y ∧ r y z → r x z

/- Theorem
$⇒$ is transitive.
-/
theorem imply_trans : transitive ((→) : Prop → Prop → Prop) :=
by {intros P Q R h hp, from h.right (h.left hp)}

/- Theorem
$≤$ is also transitive.
-/
@[simp] theorem le_trans : transitive ((≤) : ℝ → ℝ → Prop) :=
by {intros x y z h, from le_trans h.left h.right}

/- Section
2.7 Partial and Total Orders
-/

def partial_order (r : bin_rel X) := reflexive r ∧ antisymmetric r ∧ transitive r
def total (r : bin_rel X) := ∀ x y : X, r x y ∨ r y x
def total_order (r : bin_rel X) := partial_order r ∧ total r

/- 
Let's now prove that $≤$ is a total order.
-/
-- As we already have already proven that $≤$ is reflexive, symmetric, and transitive, i.e. its a partial order, we only need to show $≤$ is total to prove that $≤$ is a total order.
/- Lemma
$≤$ is total.
-/
@[simp] theorem le_total : total ((≤) : ℝ → ℝ → Prop) :=
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

/- Theorem
$≤$ is a total order.
-/
theorem le_total_order : total_order ((≤) : ℝ → ℝ → Prop) :=
begin
-- As $≤$ is a partial order and is total, it is a total order!
    repeat {split},
    repeat {simp},
end

/- Section
2.7 Equivalence Relations
-/

def equivalence (r : bin_rel X) := reflexive r ∧ symmetric r ∧ transitive r

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
theorem R_refl : reflexive R :=
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
theorem R_symm : symmetric R :=
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
theorem R_trans : transitive R :=
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
theorem R_equiv : equivalence R :=
begin
-- This follows directly from lemma (1), (2), and (3).
    repeat {split},
    {from R_refl},
    {from R_symm},
    {from R_trans}
end

/-
Example 4. Let $X$ be a set of sets, where $A, B ∈ X$. Let's define $<~$ such that $A <~ B$ if an only if $∃ g: A → B$, $g$ is an injection.
-/

def brel (A B : Type*) := (∃ g : A → B, function.bijective g)
infix ` <~ `: 50 := brel

/- Theorem
$<~$ is reflexive.
-/
theorem brel_refl : reflexive (<~) := 
begin
    choose g hg using,
end

/-
Example 5.
-/

end M40001_3