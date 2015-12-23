import algebra.ordered_field algebra.blast

set_option trace.app_builder true
set_option trace.blast.arith.heuristic false
set_option blast.strategy "arith_heuristic"

namespace test_comm_ring

universe l
constants (A : Type.{l}) (s : linear_ordered_comm_ring A)
attribute s [instance]

constants (x y z w : A)

example : 0 < 1 * y + 1 → 0 < (-1) * y + -1 → false := by blast
example : 0 < 2 * y + 2 → 0 < (-1) * y + -1 → false := by blast
example : 0 < 2 * y → 0 < (-1) * y → false := by blast
example : 0 < 1 * x + 2 * y →  0 < 2 * y + (-1) * x → 0 < (-1) * y → false := by blast
example : 0 < (-3) * x + ((-7) * y + 4) → 0 < 2 * x + -3 → 0 ≤ 1 * y → false := by blast
example : 0 < 1 * w → 0 ≤ 2 * w → 0 < 3 * w → 0 < (-3) * x + ((-7) * y + 4) → 0 < 2 * x + -3 → 0 ≤ 1 * y → false := by blast

end test_comm_ring

namespace test_field

universe l
constants (A : Type.{l}) (s : linear_ordered_field A)
attribute s [instance]

constants (x y z w : A)
constants (x_neq_0 : x ≠ 0) (y_neq_0 : y ≠ 0) (z_neq_0 : z ≠ 0) (w_neq_0 : w ≠ 0)

attribute [intro] x_neq_0 y_neq_0 z_neq_0 w_neq_0

example : 0 < x * x⁻¹ * -2 → 0 < y → false := by blast
example : -(1 * x)⁻¹ < 0 → (3 * x⁻¹ * x) < 0 → false := by blast
example : (0:A) < -(1 * 2⁻¹) → false := by blast
example : 0 < -(1 * 2⁻¹)⁻¹ * -(1 * 1⁻¹ * x * 2⁻¹ + -0) →  0 < - - - x → false := by blast
example : 0 < -(3 * x * x⁻¹)⁻¹ → false:= by blast
example : 0 < (x * x⁻¹ * y) → 0 < -y → false := by blast
example : (x * x⁻¹ * y * y⁻¹)⁻¹ < 0 →  false:= by blast


example : 0 < y⁻¹ * 3 * z⁻¹ * y + 3 → 0 < (-1 * 4⁻¹) * z⁻¹ * y * y⁻¹ + -1 * 4⁻¹ → false := by blast
example : 0 < 2 * 4⁻¹ * y * z⁻¹ + 3 * 6⁻¹ → 0 < (-1) * y * z⁻¹ + -1 → false := by blast
example : 0 < 2⁻¹ * y⁻¹ → 0 < (-1) * y⁻¹ → false := by blast

example : 0 < 3 * y⁻¹ * z⁻¹ * w → 0 < 3 * y⁻¹ * (- z)⁻¹ * w → false := by blast

example : 0 < 44 * x + 33 * y →
          0 ≤ -33 * x⁻¹ + (11⁻¹ + (2 * 3⁻¹ * 1)⁻¹ * x⁻¹) → 0 ≤ (y⁻¹ * x)⁻¹ * 11 → 0 < -11 * x + 40 * y → 0 < z * z → 0 < z⁻¹ * z⁻¹
          → 0 < 10 * y⁻¹ → 0 < 3 * x + - 7 * y⁻¹ + - 7 * y → 0 < -x + y → 0 ≤ y⁻¹ + x⁻¹ + x + y → 0 ≤ -7 * y⁻¹ + - 6 * z⁻¹ → false := by blast

example : 0 < 44 * x + 33 * y + 11 * z →
          0 ≤ -33 * x⁻¹ + (11⁻¹ + (2 * z * 3⁻¹ * 1)⁻¹ * x⁻¹) → 0 ≤ z + (y⁻¹ * x)⁻¹ * 11 → 0 < -z + -11 * x + 40 * y → 0 < z * z → 0 < z⁻¹ * z⁻¹
          → 0 < 10 * y⁻¹ → 0 < 3 * x + - 7 * y⁻¹ + - 7 * y + 7 * z → 0 < -x + (y + - 2 * z) →
          0 ≤ y⁻¹ + x⁻¹ + x + y + z→ 0 ≤ -7 * y⁻¹ + - 6 * z⁻¹ → false := by blast

example : 0 < 44 * x + 33 * y + 11 * z  + w + w⁻¹ → 0 < w + w⁻¹ + x → 0 < w + - w⁻¹ + - x → 0 < z + w → 0 < 11 * w + 13 * z → 0 < 11 * w⁻¹ + -z⁻¹
          → 0 ≤ -33 * x⁻¹ + (11⁻¹ + 7 * w + (2 * z * 3⁻¹ * 1)⁻¹ * x⁻¹) + w⁻¹ + x → 0 < z + - w⁻¹ → 0 < x + -z⁻¹ + - w⁻¹
          → 0 ≤ z + (y⁻¹ * x)⁻¹ * 11 + - 8 * w → 0 < -z + -11 * x + 30 * w + 40 * y + 3 * w⁻¹ → 0 < z * z → 0 < z⁻¹ * z⁻¹ + w + x → 0 < z
          → 0 < 10 * y⁻¹ + - 11 * w → 0 < 3 * x + - 7 * y⁻¹ + z⁻¹ + - 7 * y + -w + 7 * z + 3 * w⁻¹ → 0 < -x + (y + - 2 * z) + 7 * w⁻¹ + 7 * w
          → 0 ≤ y⁻¹ + x⁻¹ + x + y + z + - 2 * w → 0 ≤ -7 * y⁻¹ + - 6 * z⁻¹ + - w⁻¹ → 0 < w →  0 < w⁻¹ → 0 < x
          →  0 ≤ y + x + x⁻¹ → 0 < 3 * y + - x →  0 < - 3 * y + z + x → 0 < - w⁻¹ + - z → false := by blast

example : 0 < 44 * x * x + 33 * y + 11 * z  + w + w⁻¹ → 0 < w * w + w⁻¹ + x → 0 < w + - w⁻¹ + - x * x → 0 < z + w
          → 0 < 11 * w * y + 13 * z → 0 < 11 * w⁻¹ + -z⁻¹
          → 0 ≤ -33 * x⁻¹ + (11⁻¹ + 7 * w + (2 * z * 3⁻¹ * 1)⁻¹ * x⁻¹) + w⁻¹ + x → 0 < z + - w⁻¹ → 0 < x * x + -z⁻¹ + - w⁻¹ * z
          → 0 ≤ z + (y⁻¹ * x)⁻¹ * 11 + - 8 * w * w * y → 0 < -z * z * w⁻¹ + -11 * x * x + 30 * w + 40 * y + 3 * w⁻¹
          → 0 < z * z → 0 < z⁻¹ * z⁻¹ + w + x → 0 < z * x * w
          → 0 < 10 * w * y⁻¹ + - 11 * w * x * w
          → 0 < 3 * x * y + - 7 * y⁻¹ + z⁻¹ + - 7 * y + -w + 7 * z + 3 * w⁻¹ → 0 < -x + (y + - 2 * z) + 7 * w⁻¹ + 7 * w
          → 0 ≤ y⁻¹ + x⁻¹ + x + y * y + z + - 2 * w → 0 ≤ -7 * y⁻¹ + - 6 * z⁻¹ + - w⁻¹
          → 0 < w * w →  0 < y * w⁻¹ → 0 < x * x * z
          →  0 ≤ y + x + x⁻¹ → 0 < 3 * y + - x →  0 < - 3 * y⁻¹ + z + x * x → 0 < - w⁻¹ + - z*z
          → 0 < z + w + x + y + x*x → z + w < w * x → z + w * x < z⁻¹ → z⁻¹ + x⁻¹ ≤ y⁻¹
          → false := by blast

-- TODO(dhs): discover equalities and communicate them to the state
example : 2 * x + 3 * y = 11 →  x + 7 * y = 13 → y < 15 * 11⁻¹ → false := by blast
example : 2 * x + 3 * y = 11 →  x + 7 * y = 13 → y > 15 * 11⁻¹ → false := by blast
example : 2 * x + 3 * y = 11 →  x + 7 * y = 13 → x < 3 → false := by blast

end test_field
