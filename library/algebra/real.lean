import algebra.sequence
open sequence

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

  -- prove ℝ is an ordered, dedekind-complete field

end real

   
