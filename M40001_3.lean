-- begin header
import tactic.ring
import data.real.basic
import data.setoid
import tactic.linarith
import tactic.norm_cast

namespace M40001_3
-- end header

/-Section
2.5 Binary Relations
-/

variable {X : Type}
def bin_rel (R : Type) := X → X → Prop

def reflexive (r : setoid X) := ∀ x : X, r.rel x x
def symmetric (r : setoid X) := ∀ x y : X, r.rel x y → r.rel y x
def antisymmetric (r : setoid X) := ∀ x y : X, r.rel x y ∧ r.rel y x → x = y
def trainsitive (r : setoid X ) := ∀ x y z : X, r.rel x y ∧ r.rel y z → r.rel x z

def partial_order (r : setoid X) := reflexive r ∧ symmetric r ∧ transitive r.rel
def total (r : setoid X) := ∀ x y, r.rel x y ∨ r.rel y x
def total_order (r : setoid X) := partial_order r ∧ total r

def equivalence (r : setoid X) := reflexive r ∧ symmetric r ∧ transitive r.rel

def class (s : X) (r : setoid X) := {x : X ∧ r.rel s x} -- huh


end M40001_3