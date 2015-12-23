import algebra.ordered_field algebra.blast

universe l
constants (A : Type.{l}) (s : linear_ordered_field A)
constants (x y z w : A)

attribute s [instance]
attribute inv [light 3]

set_option trace.app_builder true
set_option trace.blast.arith.normalize.error true

#arith_normalize 1 (5:A)
#arith_normalize 1 (5:A) + 7
#arith_normalize 1 (5:A) * 1 * 2 + 7 * 2 + 0 * 5 + 77
#arith_normalize 1 x
#arith_normalize 1 - x
#arith_normalize 1 - - x
#arith_normalize 1 - - - x
#arith_normalize 1 x * y
#arith_normalize 1 x * y * z
#arith_normalize 1 (x * y * z) * w
#arith_normalize 1 (x * y) * (z * w)
#arith_normalize 1 (x * (y * y)) * z
#arith_normalize 1 (x * (y * y)) * (z * w) * z
#arith_normalize 1 (x * 2 * 3)
#arith_normalize 1 ((2:A) * 3)
#arith_normalize 1 x⁻¹
#arith_normalize 1 x * (x⁻¹ * z)
#arith_normalize 1 x * (x⁻¹ * w)
#arith_normalize 1 w * (x * x⁻¹)
#arith_normalize 1 w * (x * x⁻¹) * z
#arith_normalize 1 x * x⁻¹ * z * z⁻¹
#arith_normalize 1 x * (x⁻¹ * (z * w)) * z⁻¹
#arith_normalize 1 (w * x) * y
#arith_normalize 1 w * (x * x⁻¹) * w⁻¹ * z
#arith_normalize 1 w * (x * x⁻¹) * w⁻¹ * z * x * z⁻¹ * w * w⁻¹
#arith_normalize 1 -w * (x * 15⁻¹ * x⁻¹) * w⁻¹ * 5 * -3 * z * -x * z⁻¹ * w * w⁻¹ * 2
#arith_normalize 1 (1:A) / 15
#arith_normalize 1 (-1:A) / 15
#arith_normalize 1 (3:A) / 15
#arith_normalize 1 (-3:A) / 15
#arith_normalize 1 x + y + y + z + -y + z + -x + 2*x
#arith_normalize 1 ((x * y) * (z * 5 * 4 * y * z)) * (z * (4 + 4) * w)
#arith_normalize 1 (x + y) * z
#arith_normalize 1 x * (y + z)
#arith_normalize 1 (x + y) * (w + z) * (w + x * (z + w))
#arith_normalize 1 x + (y * (z + (w * (z + x))))
#arith_normalize 1 x + y + (y + z + w) + (y + z)
#arith_normalize 1 x * y * (y * z * w) * (y * z)
#arith_normalize 1 x + y + (y + z + w) + (y + z)
#arith_normalize 1 x * y * (y * z * w) * (y * z) * (y + z⁻¹ * (4 * z * x⁻¹ * 3⁻¹)⁻¹ + w⁻¹⁻¹)
#arith_normalize 1 (y * (z + (w * (z + x))))
#arith_normalize 1 (x + y + z) * w
#arith_normalize 1 (y * (z + (w * (z + x))))
#arith_normalize 1 ((x + y) * (x + y)) * (x + y)
#arith_normalize 1 (x + y) * (w + z * 6) * (5 * w + x * (- z + w)) * (x + (- y * (w + z))) + 100 * x * w * w * x
#arith_normalize 1 1 * x
#arith_normalize 1 1 * 1 * x
#arith_normalize 1 1 * x * 1
#arith_normalize 1 1 * x * 1 + 0 * x
#arith_normalize 1 0 * x
#arith_normalize 1 (0:A) + 0
#arith_normalize 1 (0:A) + 0 * 1
#arith_normalize 1 (0:A) * 1
#arith_normalize 1 (1:A) * 1 + 0 + 0 * 1 * 1 + 1 * 0 * x
#arith_normalize 1 x + y * z + w + 1 * x + 2 * y * z + 0 * y
#arith_normalize 1 (0:A) * 1 * x
#arith_normalize 1 (0:A) * x * x
#arith_normalize 1 (0:A) * 1 * x
#arith_normalize 1 (0:A) * 1 * 1 * 1 * 1 * x
#arith_normalize 1 x + (y * z * 3⁻¹ * 4)
#arith_normalize 1 x + - x
#arith_normalize 1 0 + x + - x + y + - y
#arith_normalize 1 2 * (-1 * y) + 1 * (2 * y + -x)
#arith_normalize 1 -2 * y + 0 + 2 * y + - x
#arith_normalize 1 0 + 0 + -2 * y + 2 * y + y
#arith_normalize 1 (2 * (-1 * y + -0) + 1 * (2 * y + -1 * x + -0))
#arith_normalize 1 0 + 5 * x
#arith_normalize 1 1 * (-1 * y + -1 + -0) + 1 * (1 * y + 1 + -0)
#arith_normalize 1 0 + 0 * 1 * y
#arith_normalize 1 0 + 5 * x
#arith_normalize 1 1 * (-1 * y⁻¹ + -5⁻¹ + -0) + 1 * (1 * y + 1 + -0)⁻¹
#arith_normalize 1 0 + 0 * 1 * y
#arith_normalize 1 (3:A) * (3⁻¹ * 1)⁻¹
#arith_normalize 1 (x * y)
#arith_normalize 1 (x * y)⁻¹
#arith_normalize 1 (x * y)⁻¹⁻¹⁻¹
#arith_normalize 1 (x⁻¹ * y)⁻¹⁻¹⁻¹ * (x + y⁻¹ + 5⁻¹ + 1⁻¹)
#arith_normalize 1 (x * y)⁻¹⁻¹⁻¹
#arith_normalize 1 4 * (-1 * 4⁻¹ * z * y⁻¹ * y + -1 * 4⁻¹ + -0)
#arith_normalize 1 4 * (-1 * 4⁻¹ * z * y⁻¹ * y + -1 * 4⁻¹ + -0) + 1 * 3⁻¹ * (3 * y⁻¹ * z * y + 3 + -0)
#arith_normalize 1 (2:A) * (5 + w) * 3
#arith_normalize 1 (2:A) * 3 * (5 + w)
#arith_normalize 1 (2:A) * 3⁻¹ * (5 + z)
#arith_normalize 1 1 * 3⁻¹ * (3 * y⁻¹ * z * y + 3)
#arith_normalize 1 (3:A) * (3 + (x * y) * 1)
#arith_normalize 1 ((2:A) + x) * 3 * 5
#arith_normalize 1 1 * 2 * x
#arith_normalize 1 (1 * 2 *  x * 1)
#arith_normalize 1 ((2:A) * x * 1) * 3 * 5
#arith_normalize 1 (2:A) * (3 + w) * 5
#arith_normalize 1 x * y
#arith_normalize 1 y * x
#arith_normalize 1 -((1:A) * 2)
#arith_normalize 1 -((1:A) * 2)⁻¹
#arith_normalize 1 -((1:A) * 2⁻¹)⁻¹
#arith_normalize 1 (-(1:A) * 2⁻¹)
#arith_normalize 1 -(-(1:A) * 2⁻¹)⁻¹
#arith_normalize 1 -((1:A) * 2⁻¹) + -0
#arith_normalize 1 -(2:A)⁻¹
#arith_normalize 1 -1 * y + 1 * (x * (y * x⁻¹))
#arith_normalize 1 1 * (-y + -0) + 1 * (x * x⁻¹ * y + -0)
