import algebra.field

universe l
constants (A : Type.{l}) (s : field A)
attribute s [instance]
constants (x y z w : A)

#arith_normalize_poly 1
#arith_normalize_poly x
#arith_normalize_poly x + 1
#arith_normalize_poly x + 1 + 1
#arith_normalize_poly 1 + x + 1
#arith_normalize_poly x * x⁻¹
#arith_normalize_poly x + x*x + x + 1
#arith_normalize_poly (x + 1) * (x + 1)
#arith_normalize_poly (x * y + x⁻¹ * y⁻¹) * (x⁻¹ + y⁻¹)
#arith_normalize_poly x + x*y + y⁻¹ + y
#arith_normalize_poly (x + x*y + y⁻¹ + y) * 2
#arith_normalize_poly (x + x*y + y⁻¹ + y) * (2 + y⁻¹)
#arith_normalize_poly (x + -y + -2) * - (z + 1)
#arith_normalize_poly -(x+y)⁻¹
#arith_normalize_poly - -(x⁻¹)⁻¹ + - y⁻¹
#arith_normalize_poly 1 * 2⁻¹ + 4 * x * 5⁻¹
#arith_normalize_poly (1 * 2⁻¹ + x) * (x * 5⁻¹)
