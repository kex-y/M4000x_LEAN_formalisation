-- begin header
import M40001.M40001_C2

namespace M40001
-- end header

universe u
variables {X V : Type u}

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

lemma class_relate_lem_c 
    (s t : X) (R : bin_rel X) (h : equivalence R) : R s t ↔ cls R t = cls R s :=
begin
    split,
    {from class_relate_lem_b s t R h},
    {intro ha,
    unfold cls at ha,
    have : t ∈ {x : X | R t x}, by {rwa set.mem_set_of_eq, from equiv_refl R h t},
    rwa [ha, set.mem_set_of_eq] at this
    }
end

variable {R : bin_rel X}
def Rf (g : X → V) (s t : X)  := g s = g t

theorem equiv_relation_equiv (f = λ x, cls R x) (h : equivalence R) : ∀ s t : X, R s t ↔ Rf f s t :=
begin
    intros s t,
    unfold Rf, rw H, simp,
    split,
    {intro ha,
    rwa [←class_relate_lem_c, equiv_symm R h t s],
    assumption
    },
    {intro ha,
    rwa [class_relate_lem_c s t R h, ha]
    }
end

end M40001