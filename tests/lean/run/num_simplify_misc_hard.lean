import algebra.ordered_field

universe l
constants (A : Type.{l}) (s : linear_ordered_field A)
attribute s [instance]

set_option trace.app_builder true
--set_option trace.blast.num true

-- TODO(dhs): depends on the numeral-inverse lemmas
/-
#num_simplify (1:A) + (2 * 7)⁻¹ * (3 + 4⁻¹ + 7)⁻¹ * 2⁻¹ * (3 * 7⁻¹) + 5
#num_simplify (1:A) + (2 * 7)⁻¹ * (3 + (3 * 4⁻¹) + 7)⁻¹ * 2⁻¹ * (3 * 7⁻¹) + 5
#num_simplify (1:A) + (2 + 3 * 7⁻¹ * (7⁻¹)⁻¹ + 1 + 2 * 7)⁻¹ * (3 + (3 * 4⁻¹) + 7)⁻¹ * 2⁻¹ * (3 * 7⁻¹) + 5
#num_simplify (1:A) + (2 + 3 * 7⁻¹ * (7⁻¹)⁻¹ + (3⁻¹ + 1) + 2 * 7)⁻¹ * (3 + (3 * 4⁻¹) + 7)⁻¹ * 2⁻¹ * (3 * 7⁻¹) + 5
#num_simplify (1:A) + 1000 * (1000 + 1000⁻¹)
-/
