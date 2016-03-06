/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

truncating an ∞-group to a group
-/

import hit.trunc algebra.group

open eq is_trunc trunc

namespace algebra

  section
  parameters (n : trunc_index) {A : Type} (mul : A → A → A) (inv : A → A) (one : A)
    (mul_assoc : ∀a b c, mul (mul a b) c = mul a (mul b c))
    (one_mul : ∀a, mul one a = a) (mul_one : ∀a, mul a one = a)
    (mul_left_inv : ∀a, mul (inv a) a = one)

  local abbreviation G := trunc n A

  include mul
  definition trunc_mul [unfold 9 10] (g h : G) : G :=
  begin
    induction g with p,
    induction h with q,
    exact tr (mul p q)
  end

  omit mul include inv
  definition trunc_inv [unfold 9] (g : G) : G :=
  begin
    induction g with p,
    exact tr (inv p)
  end

  omit inv include one
  definition trunc_one [constructor] : G :=
  tr one

  local notation 1 := trunc_one
  local postfix ⁻¹ := trunc_inv
  local infix * := trunc_mul

  parameters {mul} {inv} {one}
  omit one include mul_assoc
  theorem trunc_mul_assoc (g₁ g₂ g₃ : G) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    induction g₁ with p₁,
    induction g₂ with p₂,
    induction g₃ with p₃,
    exact ap tr !mul_assoc,
  end

  omit mul_assoc include one_mul
  theorem trunc_one_mul (g : G) : 1 * g = g :=
  begin
    induction g with p,
    exact ap tr !one_mul
  end

  omit one_mul include mul_one
  theorem trunc_mul_one (g : G) : g * 1 = g :=
  begin
    induction g with p,
    exact ap tr !mul_one
  end

  omit mul_one include mul_left_inv
  theorem trunc_mul_left_inv (g : G) : g⁻¹ * g = 1 :=
  begin
    induction g with p,
    exact ap tr !mul_left_inv
  end

  omit mul_left_inv
  theorem trunc_mul_comm (mul_comm : ∀a b, mul a b = mul b a) (g h : G)
    : g * h = h * g :=
  begin
    induction g with p,
    induction h with q,
    exact ap tr !mul_comm
  end

  parameters (mul) (inv) (one)

  definition trunc_group [constructor] : group (trunc 0 A) :=
  ⦃group,
    mul          := algebra.trunc_mul          0 mul,
    mul_assoc    := algebra.trunc_mul_assoc    0 mul_assoc,
    one          := algebra.trunc_one          0 one,
    one_mul      := algebra.trunc_one_mul      0 one_mul,
    mul_one      := algebra.trunc_mul_one      0 mul_one,
    inv          := algebra.trunc_inv          0 inv,
    mul_left_inv := algebra.trunc_mul_left_inv 0 mul_left_inv,
   is_set_carrier := _⦄

  definition trunc_comm_group [constructor] (mul_comm : ∀a b, mul a b = mul b a)
    : comm_group (trunc 0 A) :=
  ⦃comm_group, trunc_group, mul_comm := algebra.trunc_mul_comm 0 mul_comm⦄

  end
end algebra
