import algebra.ordered_field

universe l
constants (A : Type.{l}) (s : linear_ordered_field A)
attribute s [instance]

-- TODO(dhs): depends on the numeral-inverse lemmas
/-
#num_simplify (1:A)⁻¹
#num_simplify (1⁻¹:A)⁻¹
#num_simplify (2:A)⁻¹
#num_simplify (2⁻¹:A)⁻¹
#num_simplify (2⁻¹:A)⁻¹⁻¹
#num_simplify ((2+2)⁻¹:A)⁻¹⁻¹
#num_simplify (3⁻¹:A)⁻¹
#num_simplify (3⁻¹:A)⁻¹⁻¹
#num_simplify (4⁻¹:A)⁻¹
#num_simplify (4⁻¹:A)⁻¹⁻¹
-/
