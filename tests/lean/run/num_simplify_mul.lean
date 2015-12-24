import algebra.ordered_field

universe l
constants (A : Type.{l}) (s : linear_ordered_field A)
attribute s [instance]

-- Multiplication with negation

#num_simplify (0:A) * 0
#num_simplify (0:A) * 1
#num_simplify (0:A) * 2
#num_simplify (0:A) * 3

#num_simplify 2 * (0:A)
#num_simplify 3 * (0:A)

#num_simplify (1:A)
#num_simplify (1:A) * 0
#num_simplify (1:A) * 1
#num_simplify (1:A) * 2
#num_simplify (1:A) * 3

#num_simplify 2 * (1:A)
#num_simplify 3 * (1:A)

#num_simplify (2:A) * 2
#num_simplify (2:A) * 3
#num_simplify (2:A) * 4

#num_simplify 3 * (2:A)
#num_simplify 4 * (2:A)

#num_simplify (3:A) * 3
