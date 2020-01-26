import M40001.M40001_4
import data.equiv.basic

namespace M40001

-- set_option pp.notation false

lemma left_inv_iff_lem (X : Type*) : 
  ∀ r s : ↥{R : bin_rel X | equivalence R}, (∀ x y : X, r.1 x y ↔ s.1 x y) ↔ s = r :=
begin
  intros r s,
  split,
    {intro h,
    cases r, cases s,
    rw subtype.ext,
    dsimp,
    ext, from (h x x_1).symm,
    },
    {intros h x y,
    rw h
    }
end

def tricky (X : Type*) : {R : bin_rel X | equivalence R} ≃ {A : set (set X) | partition A} :=
{ to_fun := λ r, ⟨{a : set X | ∃ s : X, a = cls r.1 s}, equiv_relation_partition r.1 r.2⟩,
  inv_fun := λ a, ⟨rs a.1, partition_equiv_relation a.1 a.2 ⟩,
  left_inv := 
begin
    intro r,
    rcases r.2 with ⟨rrefl, ⟨rsymm, rtran⟩⟩,
    rw ←left_inv_iff_lem,
    intros x y,
    split,
      {intro h, simp,
      use cls r.val x,
      split,
        {use x},
        {split, apply rrefl, from h
        },
      },
      {intro h, simp at h,
      rcases h with ⟨B, ⟨⟨z, hb⟩, ⟨xB, yB⟩⟩⟩,
      unfold cls at hb,
      have h1 : r.val x z, by {apply rsymm, rw hb at xB, rwa set.mem_set_of_eq at xB},
      have h2 : r.val z y, by {rw hb at yB, rwa set.mem_set_of_eq at yB},
      from rtran x z y ⟨h1, h2⟩
      }
end,
  right_inv := 
begin
  unfold function.right_inverse,
  unfold function.left_inverse,
  intro b, simp,
  unfold cls,
  rw subtype.ext,
  ext,
  split,
    {rintro ⟨s, h⟩,
    rw h,
    have h1 : equivalence (rs (b.val)) := partition_equiv_relation b.val b.2,
    have h2 : ∀ x y : X, rs (b.val) x y = ∃ B ∈ b.val, x ∈ B ∧ y ∈ B, by {intros x y, refl},
    sorry
    },
  sorry
end
}


end M40001