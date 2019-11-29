-- begin header
import tactic.ring
import data.real.basic

namespace M40001
-- end header

open function 
universe u

/- Section
2.2.1 Function Composition
-/

/- Theorem
Given two functions $f : A → B$, $g : B → C$ where $A, B, C$ are sets, then $(g ∘ f)(x)$ (the composition of $g$ and $f$) is $g(f(x))$.
-/
theorem composition
    (A B C : Type u) (f : A → B) (g : B → C) (x : A) : (g ∘ f)(x) = g(f(x)) :=
begin
    -- This is true by definition!
    refl,
end

/- Section
2.3 Injectivity, Surjectivity and Bijectivity
-/

/-Theorem
A function $f : X → Y$ is called injective if distinct elements of $X$ get mapped to distinct elements of $Y$. More formally, $f$ is injective if $∀ a, b ∈ X, f(a) = f(b) ⇒ a = b$.
-/
theorem injective_def 
    (X Y : Type u) (f : X → Y) : injective f ↔ (∀ a b : X, f(a) = f(b) → a = b) :=
begin
    -- This is true by definition!
    refl,
end

/- Theorem
A function $f : X → Y$ is called surjective if every element of $Y$ gets "hit" by $f$. More formally, $f$ is surjective if $∀ y ∈ Y, ∃ x ∈ X$ such that $f(x) = y$.
-/
theorem surjective_def 
    (X Y : Type u) (f : X → Y) : surjective f ↔ ∀ y : Y, ∃ x : X, f(x) = y :=
begin
    -- This is true by definition!
    refl,
end

/- Theorem
A function $f : X → Y$ is called bijective if it is both injective and surjective.
-/
theorem bijective_def
    (X Y : Type u) (f : X → Y) : bijective f ↔ injective f ∧ surjective f :=
begin
    -- This is true by definition!
    refl,
end

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
    -- By definition, we have $(g ∘ f)(x) = g(f(x))$, so we have $g (f(a)) = g (f(b))$.
    repeat {rw composition at ha},
    -- Since $g$ is injective, we have $f(a) = f(b)$.
    apply h.left,
    -- Similarly, since $f$ is injective, $a = b$, which is exactly what we wanted!
    apply h.right,
    assumption,
end

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
    rw [composition, hx, hy],
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
    repeat {assumption},
end

/-Section
2.4 Inverses
-/

section var0
    variables {X Y : Type u}
    def two_sided_inverse (f : X → Y) (g : Y → X) := (∀ x : X, (g ∘ f)(x) = x) ∧ (∀ y : Y, (f ∘ g)(y) = y)
end var0

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
    rw composition,
    -- Consider that since, by definition of $g$, $∀ y ∈ Y, f(g(y)) = y$ we have $f(g(f(a))) = f(a)$,
    have ha : f (g (f a)) = f a,
        rw hg (f a),
    -- therefore, as $f$ is injective, we have $f(g(f(a))) = f(a) ⇒ g(f(a)) = f(a)$. Thus, $g$ is a left inverse of $f$.
    exact hfinj ha,
    -- Now, all we have left to prove is that $g$ is a right inverse of $f$. But that is true by definition, so we are done!
    assumption,
end


end M40001