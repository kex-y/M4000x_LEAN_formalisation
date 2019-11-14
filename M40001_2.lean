-- begin header
import tactic.ring
import data.real.basic
import tactic.linarith
import tactic.library_search
import tactic.norm_cast

namespace M40001_2
-- end header

open function 

/- Section
2.2.1 Function Composition
-/

theorem composition
    (A B C : Type) (f : A → B) (g : B → C) (x : A) : (g ∘ f)(x) = g(f(x)) :=
begin
    -- This is true by definition!
    refl,
end

/- Section
2.2.2 Equality of Functions
-/

theorem equality 
    (A B : Type) (f₁ f₂ : A → B) : ∀ x : A, f₁(x) = f₂(x) ↔ f₁ = f₂ :=
begin
    intro x,
    split,

end

/- Section
2.3 Injectivity, Surjectivity and Bijectivity
-/

theorem injective_def 
    (X Y : Type) (f : X → Y) : injective f ↔ (∀ a b : X, f(a) = f(b) → a = b) :=
begin
    -- This is true by definition!
    refl,
end

theorem surjective_def 
    (X Y : Type) (f : X → Y) : surjective f ↔ ∀ y : Y, ∃ x : X, f(x) = y :=
begin
    -- This is true by definition!
    refl,
end

theorem bijective_def
    (X Y : Type) (f : X → Y) : bijective f ↔ injective f ∧ surjective f :=
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
    (X Y Z : Type) (f : X → Y) (g : Y → Z) : injective f ∧ injective g → injective (g ∘ f) :=
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
    (X Y Z : Type) (f : X → Y) (g : Y → Z) : surjective f ∧ surjective g → surjective (g ∘ f) :=
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
    (X Y Z : Type) (f : X → Y) (g : Y → Z) : bijective f ∧ bijective g → bijective (g ∘ f) :=
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

section test
    variables {X Y : Type}
    def two_sided_inverse (f : X → Y) (g : Y → X) := ∀ x : X, (g ∘ f)(x) = x ∧ ∀ y : Y, (f ∘ g)(y) = y
end test

/-Theorem
A function $f : X → Y$ has a two-sided inverse if and only if it is a bijection.
-/
theorem exist_two_sided_inverse
    (X Y : Type) (f : X → Y) : ∃ g : Y → X, two_sided_inverse f g ↔ bijective f :=
begin
    
end

end M40001_2