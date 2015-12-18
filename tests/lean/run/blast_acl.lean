import algebra.ordered_field

namespace test_comm_ring

universe l
constants (A : Type.{l}) (s : linear_ordered_comm_ring A)
attribute s [instance]

constants (x y z w : A)

set_option blast.strategy "acl"
set_option trace.app_builder true

example : 0 < 1 * y + 1 → 0 < (-1) * y + -1 → false := by blast
example : 0 < 2 * y + 2 → 0 < (-1) * y + -1 → false := by blast
example : 0 < 2 * y → 0 < (-1) * y → false := by blast
example : 0 < 1 * x + 2 * y →  0 < 2 * y + (-1) * x → 0 < (-1) * y → false := by blast
example : 0 < (-3) * x + ((-7) * y + 4) → 0 < 2 * x + -3 → 0 ≤ 1 * y → false := by blast
example : 0 < 1 * w → 0 ≤ 2 * w → 0 < 3 * w → 0 < (-3) * x + ((-7) * y + 4) → 0 < 2 * x + -3 → 0 ≤ 1 * y → false := by blast

end test_comm_ring


namespace test_field

-- TODO(dhs): we can't stress test this until we are better at proving field equality

universe l
constants (A : Type.{l}) (s : linear_ordered_field A)
attribute s [instance]

constants (x y z w : A)
constants (x_neq_0 : x ≠ 0) (y_neq_0 : y ≠ 0) (z_neq_0 : z ≠ 0) (w_neq_0 : w ≠ 0)
attribute [simp] x_neq_0 y_neq_0 z_neq_0 w_neq_0

set_option blast.strategy "acl"

open simplifier.ac simplifier.neg simplifier.unit simplifier.distrib

example : 0 < 3 * y⁻¹ * z * y + 3 → 0 < (-1 * 4⁻¹) * z * y⁻¹ * y + -1 * 4⁻¹ → false := by blast
example : 0 < 2 * 4⁻¹ * y + 3 * 6⁻¹ → 0 < (-1) * y + -1 → false := by blast
example : 0 < 2⁻¹ * y⁻¹ → 0 < (-1) * y⁻¹ → false := by blast

end test_field
