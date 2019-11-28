-- begin header
import tactic.ring
import data.real.basic
import data.setoid
import M40001.M40001_2
import tactic.linarith
import tactic.norm_cast

namespace M40001_3
-- end header

/-Section
2.5 Binary Relations
-/
universe u
variables {X V : Type u}
def bin_rel (X : Type*) := X → X → Prop

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
lemma R_refl : reflexive R :=
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
lemma R_symm : symmetric R :=
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
lemma R_trans : transitive R :=
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

def brel (A B : Type*) := ∃ g : A → B, function.bijective g
infix ` <~ `: 50 := brel

/- Lemma
$<~$ is reflexive.
-/
@[simp] lemma brel_refl : reflexive (<~) := 
begin
-- To prove $<~$ is reflexive we need to show there exists a bijection between a set $X$ and itself.
    intro X,
-- Luckily, we can simply choose the identity function! 
    let g : X → X := id,
    existsi g,
-- Since the identity function is bijective, $<~$ is reflexive as required.
    from function.bijective_id
end

/- Lemma
$<~$ is symmetric.
-/
@[simp] lemma brel_symm : symmetric (<~) :=
begin
-- To prove $<~$ is symmetric we need to show that, for sets $X, Y$, $X <~ Y ⇒ Y <~ X$.
    intros X Y,
-- Suppose $X <~ Y$, then by definition, $∃ f : X → Y$, where $f$ is bijective.
    rintro ⟨f, hf⟩,
-- As proven ealier, $f$ is bijective implies $f$ has a two sided inverse $g$, let's choose that as our function.
    have hg : ∃ g : Y → X, M40001_2.two_sided_inverse f g,
        {rwa M40001_2.exist_two_sided_inverse
    },
    {cases hg with g hg,
    existsi g,
-- Since $g$ is bijective if and only if $g$ has a two sided inverse, it suffices to prove that such an inverse exist.
    rw ←M40001_2.exist_two_sided_inverse,
-- But as $g$ is the two sided inverse of $f$ by construction, we have $f$ is the two sided inverse of $g$ by definition, thus such an inverse does exist!
    existsi f,
    split,
    {from hg.right},
    {from hg.left}
    }
end

/- Lemma
$<~$ is transitive.
-/
@[simp] lemma brel_trans : transitive (<~) :=
begin
-- Given three sets $X, Y, Z$ where $X <~ Y$ and $Y <~ Z$ we need to show that $X <~ Z$.
    intros X Y Z,
-- Since $X <~ Y$ and $Y <~ Z$ there exists bijective functions $f : X → Y$ and $g : Y → Z$.
    rintro ⟨⟨f, hf⟩, g, hg⟩,
-- But as proven ealier, the composition of two bijective functions is also bijective. Thus, $g ∘ f : X → Z$ is a bijective function which is exactly what we need!
    existsi (g ∘ f),
    apply M40001_2.both_bijective,
    split, repeat {assumption}
end

/-
With that, we can conclude that $<~$ is an equivalence relation!
-/

/- Theorem
$<~$ is an equivalence relation
-/
theorem brel_equiv : equivalence (<~) :=
by {repeat {split}, repeat {simp} }

/-
Example 5. Let $X$ and $Y$ be two sets, and $f : X → V$ be some function between the sets. Let's define the binary relation $~>$ such that for $x, y ∈ X$ $x ~> y$ if and only if $f(x) = f(y)$.
-/

variables {M N : Type}
def crel (f : X → V) (x y : X) := f x = f y
infix ` ~> `: 50 := crel

/- Lemma
$~>$ is reflexive.
-/
@[simp] lemma crel_refl : ∀ f : X → V, reflexive ((~>) f) := 
by {intros f x, unfold crel}

/- Lemma
$~>$ is symmetric.
-/
@[simp] lemma crel_symm : ∀ f : X → V, symmetric ((~>) f) :=
begin
    intros f x y h,
    unfold crel at h,
    unfold crel,
    rwa h,
end

/- Lemma
$~>$ is transitive.
-/
@[simp] lemma crel_trans : ∀ f : X → V, transitive ((~>) f) :=
begin
    intros f x y z,
    rintro ⟨ha, hb⟩,
    unfold crel at ha hb,
    unfold crel,
    rw [ha, hb],
end

/-
Thus, since $~>$ is reflexive, symmetric and transitive, it is an equivalence relation!
-/

/- Theorem
$~>$ is an equvivalence relation.
-/
theorem crel_eq : ∀ f : X → V, equivalence ((~>) f) :=
begin
    intros f,
    unfold equivalence,
    repeat {split},
    repeat {simp},
end


end M40001_3