-- begin header
import M40001.M40001_C1
import data.real.basic

namespace M40001
-- end header

open function 
universe u

/- Section
2.2.1 Function Composition
-/

/- Definition
Given two functions $f : A → B$, $g : B → C$ where $A, B, C$ are sets, then $(g ∘ f)(x)$ (the composition of $g$ and $f$) is $g(f(x))$.
-/
def my_composition {A B C : Type u} (f : A → B) (g : B → C) := λ x : A, g (f x)

/-
Remark. Here, to define $\tt{my\_composition}$ we used something called lambda abstraction $\tt{λ x : A, g (f x)}$. 
This is essentially saying we are mapping $\tt{x}$ with type $\tt{A}$ to $\tt{g(f(x))}$. 
Read more about lambda abstraction <a href = "shorturl.at/hGPX1">here</a> or <a href = "https://en.wikipedia.org/wiki/Lambda_calculus">here<a>.
-/

/- Section
2.3 Injectivity, Surjectivity and Bijectivity
-/

/- Definition
A function $f : X → Y$ is called injective if distinct elements of $X$ get mapped to distinct elements of $Y$. More formally, $f$ is injective if $∀ a, b ∈ X, f(a) = f(b) ⇒ a = b$.
-/
def my_injective {X Y : Type u} (f : X → Y) := ∀ a b : X, f(a) = f(b) → a = b

/- Definition
A function $f : X → Y$ is called surjective if every element of $Y$ gets "hit" by $f$. More formally, $f$ is surjective if $∀ y ∈ Y, ∃ x ∈ X$ such that $f(x) = y$.
-/
def my_surjective {X Y : Type u} (f : X → Y) := ∀ y : Y, ∃ x : X, f(x) = y

/- Definition
A function $f : X → Y$ is called bijective if it is both injective and surjective.
-/
def my_bijective {X Y : Type u} (f : X → Y) := injective f ∧ surjective f

/- 
Remark. Although we have defined some lovely properties for our functions, it turns out that these definitions are already defined in the LEAN maths library.
So while our effort might be wasted, we can now use some theorems already written without going through them ourselves!
-/

/- Section
Bijectivity and Composition
-/

/-Theorem
Let $f : X → Y$ and $g : Y → Z$ be functions, then if $f$ and $g$ are both injective, then so is $g ∘ f$.
-/
theorem both_injective 
    (X Y Z : Type u) (f : X → Y) (g : Y → Z) : injective f ∧ injective g → injective (g ∘ f) :=
begin
    -- Suppose that $f$ and $g$ are injective functions, we need to show that $g ∘ f$ is also injective, i.e. if $(g ∘ f)(a) = (g ∘ f)(b)$, then $a = b$.
    intros h a b ha,
    -- Since $g$ is injective, we have $f(a) = f(b)$.
    apply h.left,
    -- Similarly, since $f$ is injective, $a = b$, which is exactly what we wanted!
    apply h.right,
    assumption
end

/-
Remark. Notice that in step 2, LEAN knew that by definition, $(g ∘ f)(x) = g(f(x))$, so we have $g (f(a)) = g (f(b))$, how smart is that!
-/

/-Theorem
Let $f : X → Y$ and $g : Y → Z$ be functions, then if $f$ and $g$ are both surjective, then so is $g ∘ f$.
-/
theorem both_surjective
    (X Y Z : Type u) (f : X → Y) (g : Y → Z) : surjective f ∧ surjective g → surjective (g ∘ f) :=
begin
    -- Suppose that $f$ and $g$ are surjective functions, we need to show that $g ∘ f$ is also surjective, i.e. $∀ z ∈ Z, ∃ x ∈ X, (g ∘ f)(x) = z$. 
    intros h z,
    -- Since $g$ is surjective, there is a $y ∈ Y$ such that $g(y) = z$.
    have ha : ∃ y : Y, g(y) = z, apply h.right,
    cases ha with y hy,
    -- Similarly, as $f$ is surjective, there is a $x ∈ X$ such that $f(x) = y$.
    have hb : ∃ x : X, f(x) = y, apply h.left,
    cases hb with x hx,
    -- But by definition, $(g ∘ f)(x) = g(f(x)) = g(y) = z$ So we are done!
    existsi x,
    rwa [←hy, ←hx]
end

/-Theorem
Let $f : X → Y$ and $g : Y → Z$ be functions, then if $f$ and $g$ are both bijective, then so is $g ∘ f$.
-/
theorem both_bijective
    (X Y Z : Type u) (f : X → Y) (g : Y → Z) : bijective f ∧ bijective g → bijective (g ∘ f) :=
begin
    -- Since $f$ and $g$ are bijective, they are also injective and surjective.
    rintro ⟨⟨hfi, hfs⟩, hgi, hgs⟩,
    split,
    -- But since $f$ and $g$ are injective, $g ∘ f$ is injective by our previous theorem.
    apply both_injective,
    split,
    repeat {assumption},
    -- Similarly, since $f$ and $g$ surjective, $g ∘ f$ is surjective.
    apply both_surjective,
    split,
    -- Hence, since $g ∘ f$ is injective and surjective, $g ∘ f$ is bijective.
    repeat {assumption}
end

/-Section
2.4 Inverses
-/

/- Definition
By digging through $\tt{functions}$, it turns out that the brilliant people of LEAN has not yet defined two sided inverse as the time of writting this. 
So let's define $g : Y → X$ to be the two sided inverse of $f : X → Y$ if and only if $∀ x ∈ X, (g ∘ f)(x) = x$ and $∀ y ∈ Y, (f ∘ g)(y) = y$.
-/
def two_sided_inverse {X Y : Type u} (f : X → Y) (g : Y → X) := (∀ x : X, (g ∘ f)(x) = x) ∧ (∀ y : Y, (f ∘ g)(y) = y)


/-Theorem
A function $f : X → Y$ has a two-sided inverse if and only if it is a bijection.
-/
theorem exist_two_sided_inverse
    (X Y : Type u) (f : X → Y) : (∃ g : Y → X, two_sided_inverse f g) ↔ bijective f :=
begin
    -- Again, since the question is in the form of 'if and only if', we need to prove both sides of the implications. 
    split,
    -- $(⇒)$ Suppose the function $f : X → Y$ has a two sided inverse $g$, we need to show that $f$ is bijective, i.e. it is injective and surjective.
    rintro ⟨g, ⟨hlinv, hrinv⟩⟩,
    -- So lets first show that $f$ is injective.
    have hfinj : injective f,
    -- Suppose we have $f(p) = f(q)$ for some $p q ∈ X$, then $f$ is injective if $p = q$.
        intros p q hf,
    -- Since $f(p) = f(q)$, we have $g(f(p)) = g(f(q))$.
        replace hf : g (f p) = g (f q), rw hf,
    -- But since $g$ is a double sided inverse of $f$, $∀ x ∈ X, g(f(x)) = x$, hence $p = g(f(p))= g(f(q)) = q$ which is exactly what we need!
        have ha : g (f p) = p := hlinv p,
        have hb : g (f q) = q := hlinv q,
        rw [ha, hb] at hf,
        assumption,
    -- Now we need to show that $f$ is surjective, i.e. $∀ y ∈ Y, ∃ x ∈ X, f(x) = y$.
    have hfbsur : surjective f,
        intro y,
    -- Since we have $g(y) ∈ X$, suppose we choose $x$ to be $g(y)$.
        existsi g y,
    -- But, as $g$ is a double inverse of $f$, $f(g(y)) = y$ which is exactly what we need!
        exact hrinv y,
    -- Thus, as $f$ is both injective and surjective, $f$ is bijective!
    split,
    all_goals {try {assumption}},
    -- $(⇐)$ Now lets prove the reverse implication, i.e. if $f$ is bijective, then $f$ has a two-sided inverse.
    rintro ⟨hfinj, hfsur⟩,
    -- Since $f$ is surjective, $∀ y ∈ Y, ∃ x ∈ X$ such that $f(x) = y$, lets choose this $x$ to be our output of $g(y)$.
    choose g hg using hfsur,
    existsi g,
    -- Now we need to show that $g$ is a double sided inverse of $f$ so let's first show that $g$ is a left inverse of $f$.
    split,
    intro a,
    -- Consider that since, by definition of $g$, $∀ y ∈ Y, f(g(y)) = y$ we have $f(g(f(a))) = f(a)$,
    have ha : f (g (f a)) = f a,
        rw hg (f a),
    -- therefore, as $f$ is injective, we have $f(g(f(a))) = f(a) ⇒ g(f(a)) = f(a)$. Thus, $g$ is a left inverse of $f$.
    exact hfinj ha,
    -- Now, all we have left to prove is that $g$ is a right inverse of $f$. But that is true by definition, so we are done!
    assumption
end

/-Section
2.5 Binary Relations
-/
variables {X V : Type u}

/- Definition
A binary relation $R$ on a set $X$ is a function $R : X^2 → \tt{Prop}$.
-/
def bin_rel (X) := X → X → Prop

/- Section 
2.6 Common Predicates on Binary Relations
-/

/- Definition
A binary relation $R$ on $X$ is called relfexive if $∀ x ∈ X, R(x, x)$.
-/
def reflexive (r : bin_rel X) := ∀ x : X, r x x

/- Theorem
$≤$ is reflexive on $ℝ$.
-/
@[simp] theorem le_refl : reflexive ((≤) : ℝ → ℝ → Prop) := 
begin
    -- To prove that the binary relation $≤$ on $ℝ$ is reflexive, we need to show given arbitary $x ∈ ℝ$, $x ≤ x$.
    intro,
    -- But this obviously true, so we're done!
    refl
end

/- Definition
A binary relation $R$ on $X$ is called symmetric if $∀a, b ∈ X, R(a, b) ⇒ R(b, a)$.
-/
def symmetric (r : bin_rel X) := ∀ x y : X, r x y → r y x

/- Theorem
$=$ is symmetric on $ℝ$.
-/
theorem eq_symm : symmetric ((=) : ℝ → ℝ → Prop) :=
begin
    -- To prove that $=$ is a symmetric binary relation on $ℝ$, we need to show that given $x = y$, $y = x$.
    intros x y h,
    -- But if $x = y$, then we can re-write $y$ as $x$ and $x$ as $y$, thus, $y = x$. 
    rwa h
end

/- Definition
A binary relation $R$ on $X$ is called antisymmetric if $∀ a, b ∈ X, R(a, b) ∧ R(b, a) ⇒ a = b$.
-/
def antisymmetric (r : bin_rel X) := ∀ x y : X, r x y ∧ r y x → x = y

/- Theorem
$≤$ is anti-symmetric on $R$.
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

/-
Remark. Notice that in the above proof I used a lot of curly bracket. This will limit the tactic state to only show the the goal within the brackets and thus also limit clutter.
Read more about how to structure LEAN proofs nicely <href = "https://leanprover.github.io/theorem_proving_in_lean/tactics.html#structuring-tactic-proofs">here</href>.
-/

/- Definition
A binary relation $R$ on $X$ is called transitive if $∀ a, b, c ∈ X, R(a, b) ∧ R(b, c) ⇒ R(a, c)$. 
-/
def transitive (r : bin_rel X) := ∀ x y z : X, r x y ∧ r y z → r x z

/- Theorem
$⇒$ is transitive on the set of propositions.
-/
theorem imply_trans : transitive ((→) : Prop → Prop → Prop) :=
begin
    -- Let $P, Q, R$ be propositions such that $P ⇒ Q$ and $Q ⇒ R$. We then need to prove that $P ⇒ R$. Suppose $P$ is true.
    intros P Q R h hp, 
    -- Then as $P ⇒ Q$, $Q$ must also be true. And again as $Q ⇒ R$, $R$ must also be true. Thus $P ⇒ R$, and we are done!
    from h.right (h.left hp)
end

/- Theorem
$≤$ is transitive on $ℝ$.
-/
@[simp] theorem le_trans : transitive ((≤) : ℝ → ℝ → Prop) :=
begin
    -- This one is a bit tricky and require us to delve into how ordering is defined on the reals in LEAN.
    intros x y z h, 
    -- However, with the power that is mathlib, we see that there is something called $\tt{le_trans}$, so why don't we just steal that for our use here!
    from le_trans h.left h.right
end

/- Section
2.7 Partial and Total Orders
-/

/-
Let $R$ be a binary relation on the set $X$.
-/

/- Definition
We call $R$ a partial order if it is reflexive, antisymmetric, and transitive.
-/
def partial_order (r : bin_rel X) := reflexive r ∧ antisymmetric r ∧ transitive r

/- Definition
We call $R$ total if $∀ a, b ∈ X, R(a, b) ∨ R(b, a)$.
-/
def total (r : bin_rel X) := ∀ x y : X, r x y ∨ r y x

/- Definition
We call $R$ a total order if it is total and a partial order.
-/
def total_order (r : bin_rel X) := partial_order r ∧ total r

/- 
Let's now prove that $≤$ is a total order. As we already have already proven that $≤$ is reflexive, symmetric, and transitive, i.e. its a partial order, we only need to show $≤$ is total to prove that $≤$ is a total order.
-/

/- Lemma
$≤$ is total on $ℝ$.
-/
@[simp] theorem le_total : total ((≤) : ℝ → ℝ → Prop) :=
begin
    -- Suppose we have $x, y ∈ ℝ$, by the trichotomy axiom, either $x < y$, $y < x$ or $x = y$.
    intros x y,
    cases lt_trichotomy x y,
    -- If $x < y$ then $x ≤ y$.
    repeat {rw le_iff_lt_or_eq},
    {left, left, assumption},
    -- If $x = y$ then also $x ≤ y$. However, if $y > x$, then we have $y ≤ x$. Thus, by considering all the cases, we see either $x ≤ y$ or $y ≤ x$. 
    {cases h, repeat { {left, assumption} <|> right <|> assumption }, rwa h}
end

/-
Remark. The last line of this LEAN proof uses something called $\tt{tactic combinators}$. Read about is <href = "https://leanprover.github.io/theorem_proving_in_lean/tactics.html#tactic-combinators">here</href>.
-/

/- Theorem
$≤$ is a total order on $ℝ$.
-/
theorem le_total_order : total_order ((≤) : ℝ → ℝ → Prop) :=
begin
    -- As $≤$ is a partial order and is total, it is a total order!
    repeat {split},
    repeat {simp}
end

/-
Remark. Notice how I tagged some of the theorems above with $\tt{@[simp]}$? This tells LEAN to try to uses theses theorems whenever I use the tactive $\tt{simp}$. Read more about it <href = "https://leanprover.github.io/theorem_proving_in_lean/tactics.html#using-the-simplifier">here</href>.
-/

/- Section
2.7 Equivalence Relations
-/

/- Definition
A binary relation $R$ on the set $X$ is called an equivalence relation if it is reflexive, symmetric, and transitive.
-/
def equivalence (r : bin_rel X) := reflexive r ∧ symmetric r ∧ transitive r

/- 
We'll present some examples of equivalence relations below.
-/

/- Definition
Suppose we define a binary relation $R(m, n)$, $m, n ∈ ℤ$, where $R(m, n)$ is true if and only if $m - n$ is even.
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

/- Definition
Let $X$ be a set of sets, where $A, B ∈ X$. Let's define $<\mathtt{\sim}$ such that $A <~ B$ if an only if $∃ g: A → B$, $g$ is an injection.
-/
def brel (A B : Type*) := ∃ g : A → B, function.bijective g
infix ` <~ `: 50 := brel

/- Lemma
$<\mathtt{\sim}$ is reflexive.
-/
@[simp] lemma brel_refl : reflexive (<~) := 
begin
    -- To prove $<\mathtt{\sim}$ is reflexive we need to show there exists a bijection between a set $X$ and itself.
    intro X,
    -- Luckily, we can simply choose the identity function! 
    let g : X → X := id,
    existsi g,
    -- Since the identity function is bijective, $<\mathtt{\sim}$ is reflexive as required.
    from function.bijective_id
end

/- Lemma
$<\mathtt{\sim}$ is symmetric.
-/
@[simp] lemma brel_symm : symmetric (<~) :=
begin
    -- To prove $<\mathtt{\sim}$ is symmetric we need to show that, for sets $X, Y$, $X <~ Y ⇒ Y <~ X$.
    intros X Y,
    -- Suppose $X <~ Y$, then by definition, $∃ f : X → Y$, where $f$ is bijective.
    rintro ⟨f, hf⟩,
    -- As proven ealier, $f$ is bijective implies $f$ has a two sided inverse $g$, let's choose that as our function.
    have hg : ∃ g : Y → X, two_sided_inverse f g,
        {rwa exist_two_sided_inverse
    },
    {cases hg with g hg,
    existsi g,
    -- Since $g$ is bijective if and only if $g$ has a two sided inverse, it suffices to prove that such an inverse exist.
    rw ←exist_two_sided_inverse,
    -- But as $g$ is the two sided inverse of $f$ by construction, we have $f$ is the two sided inverse of $g$ by definition, thus such an inverse does exist!
    existsi f,
    split,
    {from hg.right},
    {from hg.left}
    }
end

/- Lemma
$<\mathtt{\sim}$ is transitive.
-/
@[simp] lemma brel_trans : transitive (<~) :=
begin
    -- Given three sets $X, Y, Z$ where $X <~ Y$ and $Y <~ Z$ we need to show that $X <~ Z$.
    intros X Y Z,
    -- Since $X <~ Y$ and $Y <~ Z$ there exists bijective functions $f : X → Y$ and $g : Y → Z$.
    rintro ⟨⟨f, hf⟩, g, hg⟩,
    -- But as proven ealier, the composition of two bijective functions is also bijective. Thus, $g ∘ f : X → Z$ is a bijective function which is exactly what we need!
    existsi (g ∘ f),
    apply both_bijective,
    split, repeat {assumption}
end

/-
With that, we can conclude that $<\mathtt{\sim}$ is an equivalence relation!
-/

/- Theorem
$<\mathtt{\sim}$ is an equivalence relation
-/
theorem brel_equiv : equivalence (<~) :=
begin
    -- This follows as $<\mathtt{\sim}$ is reflexive, symmetric and transitive!
    repeat {split},
    repeat {simp}
end

/-
Exercise. I have defined one more binary relation $\mathtt{\sim}>$. Can you try to prove it <href = "https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FJasonKYi%2FM4000x_LEAN_formalisation%2Fmaster%2Fhtml%2FExercises%2FExercies3.lean">here</href>?
-/

/- Section
2.9 Quotients and Equivalence Classes
-/

/- Sub-section
2.9.1 Equivalence Classes
-/

/- Definition
Let $X$ be a set and let $\mathtt{\sim}$ be an equivalence relation on $X$. Let $s ∈ X$ be an arbitrary element. We define the equivalence class of $s$, written $cl(s)$ as $cl(s) = \{x ∈ X ∣ s \mathtt{\sim} x\}.
-/
def cls (r : bin_rel X) (s : X) := {x : X | r s x}

/- Lemma
(1) Let $X$ be a set and let $R$ be an equivalence relation on $X$. Then, for $s, t ∈ X$, $R(s, t) ⇒ cl(t) ⊆ cl(s)$.
-/
lemma class_relate_lem_a 
    (s t : X) (R : bin_rel X) (h : equivalence R) : R s t → cls R t ⊆ cls R s :=
begin
    -- Given that $R$ is an equivalence relation, we know that it is reflexive, symmetric and transitive.
    rcases h with ⟨href, ⟨hsym, htrans⟩⟩,
    -- Thus, given an element $x$ in $cl(t)$ (i.e. $R(t, x)$ is true), we have, by transitivit, $R(s, x)$.
    intros ha x hb,
    have hc : R t x := hb,
    replace hc : R s t ∧ R t x, by {split, repeat {assumption}},
    replace hc : R s x := htrans s t x hc,
    -- Hence $x ∈ cl(s)$ by definition.
    from hc
end

/-
With lemma (1) in place, it is quite easy to see that, not only is $cl(t) ⊆ cl(s)$, in fact, $cl(t) = cl(s)$.
-/

/- Lemma
(2) Let $X$ be a set and let $R$ be an equivalence relation on $X$. Then, for $s, t ∈ X$, $R(s, t) ⇒ cl(t) = cl(s)$.
-/
lemma class_relate_lem_b 
    (s t : X) (R : bin_rel X) (h : equivalence R) : R s t → cls R t = cls R s :=
begin
    -- By lemma (1), $cl(t) ⊆ cl(s), and thus, we only need to prove that $cl(s) ⊆ cl(t)$ in order for $cl(t) = cl(s)$.
    intro h0,
    rw le_antisymm_iff,
    split,
        all_goals {apply class_relate_lem_a,
        repeat {assumption}
        },
    -- But, since $R$ is and equivalence relation, it is symmetric.
        {rcases h with ⟨href, ⟨hsym, htrans⟩⟩,
    -- Hence, $R(s, t) ↔ R(t, s)$ which by lemma (1) implies $cl(s) ⊆ cl(t)$ as required.
        from hsym s t h0
    }
end

/- Lemma
(3) Let $X$ be a set and let $R$ be an equivalence relation on $X$. Then, for $s, t ∈ X$, $¬ R(s, t) ⇒ cl(t) ∩ cl(s) = ∅$. 
-/
lemma class_not_relate
    (s t : X) (R : bin_rel X) (h : equivalence R) : ¬ R s t → cls R t ∩ cls R s = ∅ :=
begin
    have : (cls R t ∩ cls R s = ∅) ↔ ¬ ¬ (cls R t ∩ cls R s = ∅), rwa classical.not_not, rw this,
    -- We prove by contradiction. Suppose $cl(t) ∩ cl(s) ≠ ∅$.
    intros ha hb,
    -- Then, there must be some $x$ in $cl(t) ∩ cl(s)$.
    have hx : ∃ x, x ∈ cls R t ∩ cls R s := set.exists_mem_of_ne_empty hb,
    rcases hx with ⟨x, ⟨hα, hβ⟩⟩,
    -- Thus, by definition, $R(t, x)$ and $R(s, t)$ must both be true!
    rcases h with ⟨href, ⟨hsym, htrans⟩⟩,
    have hc : R s x ∧ R x t, by {split, 
        from hβ,
        apply hsym, from hα},
    -- But this means $R(s, t)$ must also be true by transitivity, a contradiction to $¬ R(s, t)$!
    have hd : R s t, by {from htrans s x t hc},
    contradiction,
end

/-
We now formally define a partition of a set $X$
-/

/-
Partition of a set $X$ is a set $A$ of non-empty subsets of $X$ with the property that each element of $X$ is in exacctly one of the subsets.
-/
def partition (A : set (set X)) : Prop := (∀ x : X, (∃ B ∈ A, x ∈ B ∧ ∀ C ∈ A, x ∈ C → B = C)) ∧ ∅ ∉ A

lemma equiv_refl (R : bin_rel X) (h : equivalence R) (x : X): R x x :=
by {rcases h with ⟨href, ⟨hsym, htrans⟩⟩, from href x}

lemma equiv_symm (R : bin_rel X) (h : equivalence R) (x y : X): R x y ↔ R y x :=
by {rcases h with ⟨href, ⟨hsym, htrans⟩⟩, split, from hsym x y, from hsym y x}

lemma equiv_trans (R : bin_rel X) (h : equivalence R) (x y z : X): R x y ∧ R y z → R x z :=
by {rcases h with ⟨href, ⟨hsym, htrans⟩⟩, from htrans x y z}

lemma itself_in_cls (R : bin_rel X) (h : equivalence R) (x : X) : x ∈ cls R x :=
by {unfold cls, rw set.mem_set_of_eq, from equiv_refl R h x}

/- Theorem
Let $X$ be a set and let $R$ be an equivalence relation on $X$. Then the set $V$ of equivalence classes $\{cl(s) | s ∈ X\}$ for $R$ is a partition of $X$. 
-/
theorem equiv_relation_partition -- or replace the set with (set.range (cls R))
    (R : bin_rel X) (h : equivalence R) : partition {a : set X | ∃ s : X, a = cls R s} := 
begin
    -- To show that the equivalence classes of $R$ form a partition of $X$, we need to show that every $x ∈ X$ is in exactly one equivalence class of $R$, AND, none of the equivalence classes are empty.
    split,
    -- So let's first show that every $x ∈ X$ is in exactly one equivalence class of $R$. Let $y$ be and element of $X$.
    {simp, intro y,
    existsi cls R y,
    split,
    -- Then obviously $y ∈ cl(y)$ since $R(y, y)$ is true by reflexivity.
    {use y},
        {split,
            {from itself_in_cls R h y},
    -- Okay. So now we need to prove uniqueness. Suppose there is a $x ∈ X$, $x ∈ cl(y)$, we then need to show $cl(y) = cl(x)$.
            {intros C x hC hy_in_C, rw hC,
    -- But this is true by lemma (2)!
            apply class_relate_lem_b, assumption,
            have : y ∈ cls R x, rwa ←hC,
            unfold cls at this,
            rwa set.mem_set_of_eq at this}
            }
        },
    -- Now we have to prove that none of the equivalence classes are empty. But this is quite simple. Suppose there is an equivalence class $cl(x)$ where $x ∈ X$ that is empty.
    {simp, intros x hx,
    -- But then $x ∈ cl(x)$ as $R(x, x)$ is true by reflexivity. Ah ha! Contradiction! Hence, such empty equivalence class does not in fact exist! And we are done. 
    rw set.empty_def at hx,
    have : x ∈ {x : X | false}, by {rw hx, from itself_in_cls R h x},
    rwa set.mem_set_of_eq at this
    }
end

def rs (A : set (set(X))) (s t : X) := ∃ B ∈ A, s ∈ B ∧ t ∈ B

/-
Bonus. Furthermore, it turns out that if $X$ is a set and $R$ an equivalence relation on $X$. Then any partition of $X$ can form a equivalence relation.
-/

/- Theorem
Let $X$ be a set and let $R$ be an equivalence relation on $X$. Then any partition of $X$ can form a equivalence relation. 
-/
theorem partition_equiv_relation -- I have defined rs to be: def rs (A : set (set(X))) (s t : X) := ∃ B ∈ A, s ∈ B ∧ t ∈ B
    (C : set (set(X))) (h : partition C) : equivalence (rs C) :=
begin
    split,
-- Proving reflexivity
    {intro x,
    cases h with ha hb,
    replace ha : 
        ∃ (B : set X) (H : B ∈ C), x ∈ B ∧ ∀ (D : set X), D ∈ C → x ∈ D → B = D := ha x,
    rcases ha with ⟨ha, ⟨hb, ⟨hc, hd⟩⟩⟩,
    use ha, use hb,
    split,
    repeat {assumption}
    },
-- Proving symmtric
    {split,
        {rintros x y ⟨ha, ⟨hb, ⟨hc, hd⟩⟩⟩,
        use ha, use hb,
        split,
        repeat {assumption}
        },
-- Proving transitive
        {rintros x y z ⟨⟨ha, ⟨hb, ⟨hd, he⟩⟩⟩, ⟨hf, ⟨hg, ⟨hk, hl⟩⟩⟩⟩,
        use ha, use hb,
        cases h with hm hn,
        replace hm : 
            ∃ (B : set X) (H : B ∈ C), y ∈ B ∧ ∀ (D : set X), D ∈ C → y ∈ D → B = D := hm y,
        rcases hm with ⟨ho, ⟨hp, ⟨hq, hr⟩⟩⟩,
        have : hf = ha, 
            {suffices : hf = ho, {rw this, apply hr ha, repeat {assumption}},
            rwa hr hf, repeat {assumption},
            },
        split,
        {assumption},
        {rwa ←this},
        }
    }
end


end M40001