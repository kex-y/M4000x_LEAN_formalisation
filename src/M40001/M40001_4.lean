-- begin header
import tactic.ring
import data.real.basic
import tactic.linarith
import tactic.norm_cast
import M40001.M40001_3

namespace M40001_4
-- end header

/- Section
2.9 Quotients and Equivalence Classes
-/

open M40001_3

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
    (s t : X) (R : bin_rel X) (h : M40001_3.equivalence R) : R s t → cls R t ⊆ cls R s :=
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
    (s t : X) (R : bin_rel X) (h : M40001_3.equivalence R) : R s t → cls R t = cls R s :=
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
    (s t : X) (R : bin_rel X) (h : M40001_3.equivalence R) : ¬ R s t → cls R t ∩ cls R s = ∅ :=
begin
-- LEAN badly behaving saying "cls R t ∩ cls R s = ∅" not decidable :/
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
def partition (A : set (set X)) := (∀ x : X, (∃ B ∈ A, x ∈ B ∧ ∀ C ∈ A, x ∈ C → B = C)) ∧ ∅ ∉ A

lemma equiv_refl (R : bin_rel X) (h : M40001_3.equivalence R) (x : X): R x x :=
by {rcases h with ⟨href, ⟨hsym, htrans⟩⟩, from href x}

lemma itself_in_cls (R : bin_rel X) (h : M40001_3.equivalence R) (x : X) : x ∈ cls R x :=
by {unfold cls, rw set.mem_set_of_eq, from equiv_refl R h x}

/- Theorem
Let $X$ be a set and let $R$ be an equivalence relation on $X$. Then the set $V$ of equivalence classes $\{cl(s) | s ∈ X\}$ for $R$ is a partition of $X$. 
-/
theorem equiv_relation_partion -- or replace the set with (set.range (cls R))
    (R : bin_rel X) (h : M40001_3.equivalence R) : partition {a : set X | ∃ s : X, a = cls R s} := 
begin
    split,
    {simp, intro y,
    existsi cls R y,
    split,
        {existsi y, refl},
        {split,
            {from itself_in_cls R h y},
                {intros C x hC hy_in_C, rw hC,
                apply class_relate_lem_b, assumption,
                have : y ∈ cls R x, rwa ←hC,
                unfold cls at this,
                rwa set.mem_set_of_eq at this}
            }
        },
    {simp,
    intros x hx,
    rw set.empty_def at hx,
    have : x ∈ {x : X | false}, by {rw hx, from itself_in_cls R h x},
    rwa set.mem_set_of_eq at this
    }
end


end M40001_4