import algebra.field

attribute sub [reducible]
attribute div [reducible]

namespace blast
namespace arith

variable {A : Type}
variables {a b c d x x₁ x₂ y y₁ y₂ z w : A}

-- (1) Inv
lemma inv_mul_one [s : field A] (x : A) : (1 * x)⁻¹ = 1 * x⁻¹ :=
by rewrite [one_mul, one_mul]

lemma inv_mul [s : field A] (Hx : x₁ ≠ 0) (Hy : y₁ ≠ 0) (H1 : x₁⁻¹ = x₂) (H2 : y₁⁻¹ = y₂) : (x₁ * y₁)⁻¹ = x₂ * y₂ :=
by rewrite [-H1, -H2, mul.comm, mul_inv_eq Hx Hy]

lemma inv_congr [s : division_ring A] (H1 : a = b) (H2 : b⁻¹ = c) : a⁻¹ = c := by rewrite [H1, H2]
lemma neg_congr [s : add_group A] (H1 : a = b) (H2 : -b = c) : - a = c := by rewrite [H1, H2]

--- (2) Neg
lemma neg_num_mul [s : ring A] (y : A) (H : -x = z) : - (x * y) = z * y := by rewrite [-H, neg_mul_eq_neg_mul]
lemma neg_add [s : add_comm_group A] (H1 : - x = z) (H2 : -y = w) : - (x + y) = z + w :=
by rewrite [-H1, -H2, neg_add_rev, add.comm]

--- (3) Mul
lemma mul_inv_cancel [s : division_ring A] (Ha : a ≠ 0) (H : b = a⁻¹) : a * b = 1 :=
by rewrite [H, mul_inv_cancel Ha]

lemma mul_congr [s : has_mul A] (H1 : a = x) (H2 : b = y) : a * b = x * y := by rewrite [H1, H2]
lemma mul_congr_right [s : has_mul A] (a : A) (H2 : b = y) : a * b = a * y := by rewrite H2
lemma mul_congr_right_rec [s : comm_semigroup A] (H1 : b = y) (H2 : a * y = z) : a * b = z := by rewrite [H1, H2]
lemma mul_congr_rec [s : comm_semigroup A] (H1 : a = x) (H2 : b = y) (H3 : x * y = z) : a * b = z := by rewrite [H1, H2, -H3]

lemma mul_assoc [s : semigroup A] (H : a = (x * y) * z) : a = x * (y * z) := by rewrite [H, mul.assoc]
lemma mul_insert_flat [s : semigroup A] (H1 : b * c = y) (H2 : a * y = z) : (a * b) * c = z := by rewrite [-H1 at H2, -H2, mul.assoc]

lemma mul_insertion_sort [s : comm_semigroup A] (b : A) (H1 : a * c = x) : a * (b * c) = b * x := by rewrite [-H1, mul.left_comm]

lemma mul_cancel_one_right [s : monoid A] (a : A) (H : b = 1) : a * b = a := by rewrite [H, mul_one]
lemma mul_fuse_left [s : comm_semigroup A] (H1 : b = x * y) (H2 : a * x = z) : a * b = z * y := by rewrite [H1, -mul.assoc, H2]

lemma mul_cancel_left [s : field A] (Ha : a ≠ 0) (H : b = a⁻¹ * y) : a * b = y := by rewrite [H, field.mul_inv_cancel_left Ha]

lemma one_mul_rev [s : monoid A] (a : A) : a = 1 * a := by rewrite [one_mul]

lemma mul_distrib_right [s : distrib A] (H1 : a * x = z) (H2 : a * y = w) : a * (x + y) = z + w := by rewrite [-H1, -H2, left_distrib]
lemma mul_distrib_left [s : distrib A] (H1 : a * x = y) (H2 : b * x = z) : (a + b) * x = y + z := by rewrite [-H1, -H2, right_distrib]

--- Add

lemma add_congr [s : has_add A] (H1 : a = x) (H2 : b = y) : a + b = x + y := by rewrite [H1, H2]
lemma add_congr_right [s : has_add A] (a : A) (H2 : b = y) : a + b = a + y := by rewrite H2
lemma add_assoc [s : add_semigroup A] (H : a = (x + y) + z) : a = x + (y + z) := by rewrite [H, add.assoc]

lemma add_assoc_rev [s : add_semigroup A] (H : a = x + (y + z)) : a = (x + y) + z := by rewrite [H, add.assoc]

lemma add_insert_flat [s : add_semigroup A] (H1 : b + c = y) (H2 : a + y = z) : (a + b) + c = z := by rewrite [-H1 at H2, -H2, add.assoc]
lemma add_congr_right_rec [s : add_comm_semigroup A] (H1 : b = y) (H2 : a + y = z) : a + b = z := by rewrite [H1, H2]

lemma add_sort_right [s : add_comm_semigroup A] (H1 : b = y) (H2 : a + y = z) : a + b = z := by rewrite [H1, H2]
lemma add_insertion_sort [s : add_comm_semigroup A] (b : A) (H1 : a + c = x) : a + (b + c) = b + x := by rewrite [-H1, add.left_comm]

lemma add_cancel_zero_right [s : add_monoid A] (a : A) (H : b = 0) : a + b = a := by rewrite [H, add_zero]

lemma add_fuse [s : ring A] (H1 : b = x * y) (H2 : a + x = z) :  (a * y) + b = z * y := by rewrite [H1, -H2, right_distrib]

lemma add_fuse_left [s : ring A] (H1 : b = x * y + z) (H2 : a + x = w) : (a * y) + b = (w * y) + z :=
by rewrite [H1, -H2, right_distrib, add.assoc]

lemma add_fuse_num [s : ring A] (H1 : b = x) (H2 : a + x = z) : a + b = z := by rewrite [H1, H2]
lemma add_fuse_num_left [s : ring A] (H1 : b = x + y) (H2 : a + x = z) : a + b = z + y := by rewrite [H1, -H2, add.assoc]

lemma add_fuse_zero [s : ring A] (H1 : b = x * y) (H2 : a + x = 0) : (a * y) + b = 0 :=
by rewrite [H1, -right_distrib, H2, zero_mul]

lemma add_fuse_num_zero_left [s : ring A] (H1 : b = x + y) (H2 : a + x = 0) : a + b = y := by rewrite [H1, -add.assoc, H2, zero_add]
lemma add_fuse_zero_left [s : ring A] (H1 : b = x * y + z) (H2 : a + x = 0) : (a * y) + b = z :=
by rewrite [H1, -add.assoc, -right_distrib, H2, zero_mul, zero_add]

----- (3a) Mul::neg
lemma neg_mul_neg [s : ring A] (H1 : a = -c) (H2 : b = -d) : a * b = c * d :=
by rewrite [H1, H2, -neg_mul_eq_neg_mul, -neg_mul_eq_mul_neg, neg_neg]

-- TODO(dhs): the need for this intro seems like an error in the tactic framework
lemma neg_mul_pos [s : ring A] (H1 : a = -c) (H2 : b = d) : a * b = -(c * d) :=
by intro ; rewrite [H1, H2, -neg_mul_eq_neg_mul]

lemma pos_mul_neg [s : ring A] (H1 : a = c) (H2 : b = -d) : a * b = -(c * d) :=
by rewrite [H1, H2, -neg_mul_eq_mul_neg]

----- (3b) Mul::add
lemma add_mul [s : distrib A] (H1 : a = x + y) (H2: b = c) : a * b = x * c + y * c := by rewrite [H1, H2, right_distrib]
lemma mul_add [s : distrib A] (H1 : a = x) (H2: b = y + z) : a * b = x * y + x * z := by rewrite [H1, H2, left_distrib]

end arith
end blast
