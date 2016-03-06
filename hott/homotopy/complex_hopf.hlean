/-
Copyright (c) 2016 Ulrik Buchholtz and Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke

The H-space structure on S¹ and the complex Hopf fibration
 (the standard one).
-/

import .hopf .circle

open eq equiv is_equiv circle is_conn trunc is_trunc sphere_index sphere susp

namespace hopf

  definition circle_h_space [instance] : h_space S¹ :=
  ⦃ h_space, one := base, mul := circle_mul,
    one_mul := circle_base_mul, mul_one := circle_mul_base ⦄

  definition circle_assoc (x y z : S¹) : (x * y) * z = x * (y * z) :=
  begin
    induction x,
    { reflexivity },
    { apply eq_pathover, induction y,
      { exact natural_square_tr
          (λa : S¹, ap (λb : S¹, b * z) (circle_mul_base a))
          loop },
      { apply is_prop.elimo, apply is_trunc_square } }
  end

  open sphere.ops function

  definition complex_hopf : S 3 → S 2 :=
  begin
    intro x, apply @sigma.pr1 (susp S¹) (hopf S¹),
    apply inv (hopf.total S¹), apply inv (join.spheres 1 1), exact x
  end

end hopf
