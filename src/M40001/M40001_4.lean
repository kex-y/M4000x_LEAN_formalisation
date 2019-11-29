-- begin header
import M40001.M40001_3

namespace M40001
-- end header

/- Section
2.9 Quotients and Equivalence Classes
-/

universe u
variables {X V : Type u}

/- Sub-section
Equivalence Classes
-/
def cls (r : bin_rel X) (s : X) := {x : X | r s x}

/- Lemma
(1) Let $X$ be a set and let $R$ be an equivalence relation on $X$. Then, for $s, t ∈ X$, $R(s, t) ⇒ cl(t) ⊆ cl(s)$.
-/
lemma class_relate_lem_a 
    (s t : X) (R : bin_rel X) (h : equivalence R) : R s t → cls R t ⊆ cls R s :=
begin
    rcases h with ⟨href, ⟨hsym, htrans⟩⟩,
    intros ha x hb,
    have hc : R t x := hb,
    replace hc : R s t ∧ R t x, by {split, repeat {assumption}},
    replace hc : R s x := htrans s t x hc,
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
    intro h0,
    rw le_antisymm_iff,
    split,
        all_goals {apply class_relate_lem_a,
        repeat {assumption}
        },
        {rcases h with ⟨href, ⟨hsym, htrans⟩⟩,
        from hsym s t h0
    }
end

/- Lemma
(3) Let $X$ be a set and let $R$ be an equivalence relation on $X$. Then, for $s, t ∈ X$, $¬ R(s, t) ⇒ cl(t) ∩ cl(s) = ∅$. 
-/
lemma class_not_relate
    (s t : X) (R : bin_rel X) (h : equivalence R) : ¬ R s t → cls R t ∩ cls R s = ∅ :=
begin
-- LEAN saying "cls R t ∩ cls R s = ∅" not decidable :/
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
theorem equiv_relation_partion -- or replace the set with (set.range (cls R))
    (R : bin_rel X) (h : equivalence R) : partition {a : set X | ∃ s : X, a = cls R s} := 
begin
    split,
    {simp, intro y,
    existsi cls R y,
    split,
    {use y},
        {split,
            {from itself_in_cls R h y},
                {intros C x hC hy_in_C, rw hC,
                apply class_relate_lem_b, assumption,
                have : y ∈ cls R x, rwa ←hC,
                unfold cls at this,
                rwa set.mem_set_of_eq at this}
            }
        },
    {simp, intros x hx,
    rw set.empty_def at hx,
    have : x ∈ {x : X | false}, by {rw hx, from itself_in_cls R h x},
    rwa set.mem_set_of_eq at this
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