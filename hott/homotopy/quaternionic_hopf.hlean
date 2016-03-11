/-
Copyright (c) 2016 Ulrik Buchholtz and Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke

The H-space structure on S³ and the quaternionic Hopf fibration
 (using the imaginaroid structure on S⁰).
-/

import .complex_hopf .imaginaroid

open eq equiv is_equiv circle is_conn trunc is_trunc sphere_index sphere susp
open imaginaroid

namespace hopf

  definition involutive_neg_empty [instance] : involutive_neg empty :=
  ⦃ involutive_neg, neg := empty.elim, neg_neg := by intro a; induction a ⦄

  definition involutive_neg_circle [instance] : involutive_neg circle :=
  involutive_neg_susp

  definition has_star_circle [instance] : has_star circle :=
  has_star_susp

  -- this is the "natural" conjugation defined using the base-loop recursor
  definition circle_star [reducible] : S¹ → S¹ :=
  circle.elim base loop⁻¹

  definition circle_neg_id (x : S¹) : -x = x :=
  begin
    fapply (rec2_on x),
    { exact seg2⁻¹ },
    { exact seg1 },
    { apply eq_pathover, rewrite ap_id, krewrite elim_merid,
      apply square_of_eq, reflexivity },
    { apply eq_pathover, rewrite ap_id, krewrite elim_merid,
      apply square_of_eq, apply trans (con.left_inv seg2),
      apply inverse, exact con.left_inv seg1 }
  end

  definition circle_mul_neg (x y : S¹) : x * (-y) = - x * y :=
  by rewrite [circle_neg_id,circle_neg_id]

  definition circle_star_eq (x : S¹) : x* = circle_star x :=
  begin
    fapply (rec2_on x),
    { reflexivity },
    { exact seg2⁻¹ ⬝ (tr_constant seg1 base)⁻¹ },
    { apply eq_pathover, krewrite elim_merid, rewrite elim_seg1,
      apply square_of_eq, apply trans
        (ap (λw, w ⬝ (tr_constant seg1 base)⁻¹) (con.right_inv seg2)⁻¹),
      apply con.assoc },
    { apply eq_pathover, krewrite elim_merid, rewrite elim_seg2,
      apply square_of_eq, rewrite [↑loop,con_inv,inv_inv,idp_con],
      apply con.assoc }
  end

  open prod prod.ops

  definition circle_norm (x : S¹) : x * x* = 1 :=
  begin
    rewrite circle_star_eq, induction x,
    { reflexivity },
    { apply eq_pathover, rewrite ap_constant,
      krewrite [ap_compose' (λz : S¹ × S¹, circle_mul z.1 z.2)
                            (λa : S¹, (a, circle_star a))],
      rewrite [ap_compose' (prod_functor (λa : S¹, a) circle_star)
                           (λa : S¹, (a, a))],
      rewrite ap_diagonal,
      krewrite [ap_prod_functor (λa : S¹, a) circle_star loop loop],
      rewrite [ap_id,↑circle_star], krewrite elim_loop,
      krewrite (ap_binary circle_mul loop loop⁻¹),
      rewrite [ap_inv,↑circle_mul,elim_loop,ap_id,↑circle_turn,con.left_inv],
      constructor }
  end

  definition circle_star_mul (x y : S¹) : (x * y)* = y* * x* :=
  begin
    induction x,
    { apply inverse, exact circle_mul_base (y*) },
    { apply eq_pathover, induction y,
      { exact natural_square_tr 
          (λa : S¹, ap (λb : S¹, b*) (circle_mul_base a)) loop },
      { apply is_prop.elimo } }
  end

  definition imaginaroid_sphere_zero [instance]
    : imaginaroid (sphere (-1.+1)) :=
  ⦃ imaginaroid,
    neg_neg := susp_neg_neg,
    mul := circle_mul,
    one_mul := circle_base_mul,
    mul_one := circle_mul_base,
    mul_neg := circle_mul_neg,
    norm := circle_norm,
    star_mul := circle_star_mul ⦄

  local attribute sphere [reducible]
  open sphere.ops

  definition sphere_three_h_space [instance] : h_space (S 3) :=
  @h_space_equiv_closed (join S¹ S¹)
      (cd_h_space (S -1.+1) circle_assoc) (S 3) (join.spheres 1 1)

  definition is_conn_sphere_three : is_conn 0 (S 3) :=
  begin
    have le02 : trunc_index.le 0 2,
    from trunc_index.le.step
      (trunc_index.le.step (trunc_index.le.tr_refl 0)),
    exact @is_conn_of_le (S 3) 0 2 le02 (is_conn_sphere 3)
    -- apply is_conn_of_le (S 3) le02
    --   doesn't find is_conn_sphere instance
  end

  local attribute is_conn_sphere_three [instance]

  definition quaternionic_hopf : S 7 → S 4 :=
  begin
    intro x, apply @sigma.pr1 (susp (S 3)) (hopf (S 3)),
    apply inv (hopf.total (S 3)), apply inv (join.spheres 3 3), exact x
  end

end hopf
