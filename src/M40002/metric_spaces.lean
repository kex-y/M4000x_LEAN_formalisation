import data.real.basic
import M40002.M40002_C5

/-
Metric spaces with reference to Chap. 2.15 of Rudin
-/

/-
class has_group_notation (G : Type) extends has_mul G, has_one G, has_inv G

-- definition of the group structure
class group (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

class comm_group (G : Type) extends group G :=
(mul_comm : ∀ a b : G, a * b = b * a)
-/

class has_metric_space_notation (M : Type) extends has_mul M

class metric_space (M : Type) :=
(distance : M → M → ℝ)
(self_distance : ∀ p : M, distance p p = 0)
(pos_distance : ∀ p q : M, p ≠ q → 0 < distance p q)
(distance_assoc : ∀ p q : M, distance p q = distance q p)
(triangle_ineq : ∀ p q r : M, distance p q ≤ distance p r + distance r q)

variable {M : Type}

-- def neighborhood (p : metric_space M) (r : ℝ) (h : 0 < r) : set (metric_space M) := {q : metric_space M | (metric_space M).distance p q < r}