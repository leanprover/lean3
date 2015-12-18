import algebra.field

universe l
constants (A : Type.{l}) (s : field A)
attribute s [instance]
constants (x y z w : A)

#arith_simplify 1
#arith_simplify x
#arith_simplify x + 1
#arith_simplify x + 1 + 1
#arith_simplify 1 + x + 1
#arith_simplify x * x⁻¹
#arith_simplify x + x*x + x + 1
#arith_simplify (x + 1) * (x + 1)
#arith_simplify (x * y + x⁻¹ * y⁻¹) * (x⁻¹ + y⁻¹)
#arith_simplify x + x*y + y⁻¹ + y
#arith_simplify (x + x*y + y⁻¹ + y) * 2
#arith_simplify (x + x*y + y⁻¹ + y) * (2 + y⁻¹)
#arith_simplify (x + -y + -2) * - (z + 1)
#arith_simplify -(x+y)⁻¹
#arith_simplify - -(x⁻¹)⁻¹ + - y⁻¹
#arith_simplify 1 * 2⁻¹ + 4 * x * 5⁻¹
#arith_simplify (1 * 2⁻¹ + x) * (x * 5⁻¹)
