import types.sigma types.prod
import algebra.binary algebra.group
open eq eq.ops

namespace algebra

variable {A : Type}

structure distrib [class] (A : Type) extends has_mul A, has_add A :=
(left_distrib : ∀a b c, mul a (add b c) = add (mul a b) (mul a c))
(right_distrib : ∀a b c, mul (add a b) c = add (mul a c) (mul b c))

structure mul_zero_class [class] (A : Type) extends has_mul A, has_zero A :=
(zero_mul : Πa, mul zero a = zero)
(mul_zero : Πa, mul a zero = zero)

structure zero_ne_one_class [class] (A : Type) extends has_zero A, has_one A :=
(zero_ne_one : zero ≠ one)

structure semiring [class] (A : Type) extends comm_monoid A renaming
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero mul_comm→add_comm,
  monoid A, distrib A, mul_zero_class A, zero_ne_one_class A

end algebra
