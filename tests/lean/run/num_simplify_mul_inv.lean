import algebra.ordered_field

universe l
constants (A : Type.{l}) (s : linear_ordered_field A)
attribute s [instance]

-- TODO(dhs): depends on the numeral-inverse lemmas
/-
#num_simplify (2:A) * 2⁻¹ * 2
#num_simplify (4:A) * 2⁻¹
#num_simplify (2:A) * 2⁻¹
#num_simplify (6:A) * 2⁻¹
#num_simplify (3:A) * 2⁻¹ * 2
#num_simplify (3:A) * 2⁻¹ * 2 * 3⁻¹ * 4
#num_simplify (6:A) * 2⁻¹
#num_simplify (3:A) * 2⁻¹ * 2
#num_simplify (3:A)⁻¹⁻¹ * 2 * 7⁻¹
#num_simplify (0:A) + (7 * 5⁻¹)⁻¹
#num_simplify (3:A) * (3 * 2⁻¹)
#num_simplify ((3:A) * 2⁻¹) * (3 * 2⁻¹)
#num_simplify (3:A)⁻¹⁻¹ * 2 * 7⁻¹ * (7 * 5⁻¹)⁻¹
-/
