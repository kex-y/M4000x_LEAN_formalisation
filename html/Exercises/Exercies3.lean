/-
Exercise 3.
Let us define the binary relation ~> as follow:
Let X and Y be two sets, and f : X → V be some function between the sets, then ∀ x, y ∈ X, x ~> y if and only if f(x) = f(y).

Can you prove that ~> is an equivalence relation?
Replace the sorry for your proof.

Here are some basic tactics that might help : http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/tactics/guide.html
-/

universe u
variables {X V : Type u}

-- Defining crel as the aforementioned binary relation with notation ~>
def crel (f : X → V) (x y : X) := f x = f y
infix ` ~> `: 50 := crel


@[simp] lemma crel_refl : ∀ f : X → V, reflexive ((~>) f) := 
begin 
    sorry
end

@[simp] lemma crel_symm : ∀ f : X → V, symmetric ((~>) f) :=
begin
    sorry
end

@[simp] lemma crel_trans : ∀ f : X → V, transitive ((~>) f) :=
begin
    sorry
end

theorem crel_eq : ∀ f : X → V, equivalence ((~>) f) :=
begin
    sorry
end