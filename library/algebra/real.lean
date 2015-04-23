import algebra.sequence
open sequence algebra

--definition real := quot cauchy.to_setoid
notation `ℝ` := quot cauchy.to_setoid --real

section real
  variables {x y z : ℝ}

  definition add (x y : ℝ) : ℝ :=
    (quot.lift_on₂ x y (λ a b, quot.mk (a + b)) 
                       (take a b c d : cauchy_sequence, take Hab : a ≡ c, take Hcd : b ≡ d,
                         quot.sound (add.well_defined a b c d Hab Hcd)))
  infix `+` := add

  definition neg (x : ℝ) : ℝ :=
    quot.lift_on x (λ a, quot.mk (-a)) (take a b : cauchy_sequence, take Hab : a ≡ b,
                                         quot.sound (neg.well_defined a b Hab))
  prefix `-` := neg

  definition sub (x y : ℝ) : ℝ := x + -y
  infix `-` := sub

  definition mul (x y : ℝ) : ℝ := 
    (quot.lift_on₂ x y (λ a b, quot.mk (a * b)) 
                       (take a b c d : cauchy_sequence, take Hab : a ≡ c, take Hcd : b ≡ d,
                         quot.sound (mul.well_defined a b c d Hab Hcd)))
  infix `*` := mul

  definition inv (x : ℝ) : ℝ := 
    quot.lift_on x (λ a, quot.mk (a⁻¹)) (take a b : cauchy_sequence, take Hab : a ≡ b,
                                           quot.sound (inv.well_defined a b Hab)) 
  postfix `⁻¹` := inv

  -- prove ℝ is an ordered, dedekind-complete field

  definition zero := quot.mk (cauchy_sequence.mk zero_seq zero_is_cauchy)
  definition one := quot.mk (cauchy_sequence.mk one_seq one_is_cauchy)

  definition le (x y : ℝ) : Prop := sorry
  definition lt (x y : ℝ) : Prop := sorry

  notation 0 := zero
  notation 1 := one
  infix `≤` := le
  infix `<` := lt

check @linear_ordered_field.mk

  theorem add_assoc (x y z : ℝ) : x + y + z = x + (y + z) := sorry

  theorem zero_add (x : ℝ) : 0 + x = x := sorry

  theorem add_zero (x : ℝ) : x + 0 = x := sorry

  theorem neg_cancel (x : ℝ) : -x + x = 0 := sorry

  theorem add_comm (x y : ℝ) : x + y = y + x := sorry

  theorem mul_assoc (x y z : ℝ) : x * y * z = x * (y * z) := sorry

  theorem mul_comm (x y : ℝ) : x * y = y * x := sorry

  theorem one_mul (x : ℝ) : 1 * x = x := sorry

  theorem mul_one (x : ℝ) : x * 1 = x := sorry

  theorem mul_add_eq_add_mul_left (x y z : ℝ) : x * (y + z) = x * y + x * z := sorry

  theorem mul_add_eq_add_mul_right (x y z : ℝ) : (x + y) * z = x * z + y * z := sorry

  theorem le_refl (x : ℝ) : x ≤ x := sorry

  theorem le_trans (x y z : ℝ) (H1 : x ≤ y) (H2 : y ≤ z) : x ≤ z := sorry

  theorem eq_of_le (x y : ℝ) (H1 : x ≤ y) (H2 : y ≤ x) : x = y := sorry

  theorem lt_iff_le_and_ne (x y : ℝ) : x < y ↔ (x ≤ y ∧ x ≠ y) := sorry

  theorem le_add (x y : ℝ) (H : x ≤ y) : ∀ z : ℝ, z + x ≤ z + y := sorry

  theorem zero_ne_one' : (0 : ℝ) ≠ (1 : ℝ) := sorry

  theorem mul_nonpos_of_nonpos (x y : ℝ) (Hx : x ≤ 0) (Hy : y ≤ 0) : x * y ≤ 0 := sorry

  theorem mul_neg_of_neg (x y : ℝ) (Hx : x < 0) (Hy : y < 0) : x * y < 0 := sorry

  theorem lt_or_eq_iff_le (x y : ℝ) : x ≤ y ↔ x < y ∨ x = y := sorry

  theorem le_or_le (x y : ℝ) : x ≤ y ∨ y ≤ x := sorry

  theorem inv_cancel_right (x : ℝ) : x ≠ (0 : ℝ) → x * x⁻¹ = 1 := sorry

  theorem inv_cancel_left (x : ℝ) : x ≠ (0 : ℝ) → x⁻¹ * x = 1 := sorry
  
  definition real.to_lin_ord_field [instance] := linear_ordered_field.mk
    add add_assoc 0 zero_add add_zero neg neg_cancel add_comm mul mul_assoc 1 one_mul mul_one mul_add_eq_add_mul_left
    mul_add_eq_add_mul_right le le_refl le_trans eq_of_le lt lt_iff_le_and_ne le_add zero_ne_one' mul_nonpos_of_nonpos
    mul_neg_of_neg lt_or_eq_iff_le le_or_le inv inv_cancel_right inv_cancel_left mul_comm

end real
