import algebra.field
attribute neg [light 2]
attribute inv [light 2]

universe l
constants (A : Type.{l}) (s : field A)
attribute s [instance]

constants (x y z w : A)
constants (x_neq_0 : x ≠ 0) (y_neq_0 : y ≠ 0) (z_neq_0 : z ≠ 0) (w_neq_0 : w ≠ 0)
attribute [simp] x_neq_0 y_neq_0 z_neq_0 w_neq_0

open simplifier.unit
open simplifier.neg
open simplifier.ac
open simplifier.distrib

attribute add.right_inv [simp]
attribute add_neg_cancel_left [simp]

attribute division.def [simp]
attribute mul_inv_cancel [simp]
attribute field.mul_inv_cancel_left [simp]
attribute mul_inv_eq [simp]
attribute division_ring.mul_ne_zero [simp]

set_option simplify.numerals true

#simplify eq env 0 - x * (1 + 1 + 1) * x⁻¹ + (1 + 1) * y * (1 + 1 + 1) * x * z * y⁻¹ * x⁻¹ * z⁻¹ - y * x * (1 + 1 + 1) * y * x⁻¹ * y⁻¹ * y⁻¹

#simplify eq env 0 (z * x * y) / (x * y * z) + (z * z * y) / (z * y * z) + w * w * w * z * w⁻¹ * w⁻¹ * z⁻¹ * -2 * w⁻¹
