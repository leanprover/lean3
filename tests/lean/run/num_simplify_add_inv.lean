import algebra.ordered_field

universe l
constants (A : Type.{l}) (s : linear_ordered_field A)
attribute s [instance]

-- TODO(dhs): depends on the numeral-inverse lemmas
/-
#num_simplify 1 + (1:A)⁻¹
#num_simplify 1 + (2:A)⁻¹
#num_simplify (2:A)⁻¹ + 1
#num_simplify (3:A) * 2⁻¹
#num_simplify (0:A) + 1⁻¹
#num_simplify (0:A) + 2⁻¹
#num_simplify (0:A) + 3⁻¹
#num_simplify 2⁻¹ + (0:A)
#num_simplify 3⁻¹ + (0:A)
#num_simplify (1:A) + 1⁻¹
#num_simplify (1:A) + 2⁻¹
#num_simplify (1:A) + 3⁻¹
#num_simplify 2⁻¹ + (1:A)
#num_simplify 3⁻¹ + (1:A)
#num_simplify (2:A) + 2⁻¹
#num_simplify (2:A) + 3⁻¹
#num_simplify (2:A) + 4⁻¹
#num_simplify 3⁻¹ + (2:A)
#num_simplify 4⁻¹ + (2:A)
#num_simplify (3:A) + 3⁻¹

#num_simplify (4 * 3⁻¹) + (1:A)
#num_simplify (2:A) + (2⁻¹ * 3)
#num_simplify (2:A) + (2 * 3⁻¹)
#num_simplify (2:A) + (3 * 4⁻¹)
#num_simplify (3⁻¹ * 4) + (2:A)
#num_simplify (4⁻¹ * 3⁻¹) + (2:A)
#num_simplify (3:A) + 3⁻¹
-/
