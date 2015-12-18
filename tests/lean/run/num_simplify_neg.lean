import algebra.ordered_field

universe l
constants (A : Type.{l}) (s : linear_ordered_field A)
attribute s [instance]

#num_simplify -(0:A)
#num_simplify -(-0:A)
#num_simplify -(1:A)
#num_simplify -(-1:A)
#num_simplify -(2:A)
#num_simplify -(-2:A)
#num_simplify -(3:A)
#num_simplify -(-3:A)
#num_simplify -(4:A)
#num_simplify -(-4:A)
#num_simplify - - - - - - (4:A)
