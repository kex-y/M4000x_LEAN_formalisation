import M40001.M40001_C2

/-
Exercise 4.
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
    split,
-- Proving reflexivity
    {intro x,
    cases h with ha hb,
    replace ha: 
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
-- Proving transitivity
        {rintros x y z ⟨ha, ⟨hb, ⟨hd, he⟩⟩⟩ ⟨hf, ⟨hg, ⟨hk, hl⟩⟩⟩,
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