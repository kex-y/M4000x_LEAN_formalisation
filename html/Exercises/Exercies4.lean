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

def bin_rel (X) := X → X → Prop
def equivalence_rel (r : bin_rel X) := reflexive r ∧ symmetric r ∧ transitive r
def cls (r : bin_rel X) (s : X) := {x : X | r s x}

def partition (A : set (set X)) : Prop := (∀ x : X, (∃ B ∈ A, x ∈ B ∧ ∀ C ∈ A, x ∈ C → B = C)) ∧ ∅ ∉ A

def rs (A : set (set(X))) (s t : X) := ∃ B ∈ A, s ∈ B ∧ t ∈ B
-- The code above is simply used to esablish the definitions!

theorem partition_equiv_relation -- I have defined rs to be: def rs (A : set (set(X))) (s t : X) := ∃ B ∈ A, s ∈ B ∧ t ∈ B
    (C : set (set X)) (h : partition C) : equivalence_rel (rs C) :=
begin
    sorry
end