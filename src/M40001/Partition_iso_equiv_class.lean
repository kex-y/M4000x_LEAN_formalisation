import M40001.M40001_4
import data.equiv.basic

namespace M40001

def tricky (X : Type*) : {R : bin_rel X | equivalence R} ≃ {A : set (set X) | partition A} :=
{ to_fun := λ r, ⟨{a : set X | ∃ s : X, a = cls r.1 s}, equiv_relation_partition r.1 r.2⟩,
  inv_fun := λ a, ⟨rs a.1, partition_equiv_relation a.1 a.2 ⟩,
  left_inv := begin sorry end,
  right_inv := begin sorry end
}

end M40001