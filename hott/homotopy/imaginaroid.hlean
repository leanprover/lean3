/-
Copyright (c) 2016 Ulrik Buchholtz and Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke

Cayley-Dickson construction via imaginaroids
-/

import algebra.group cubical.square types.pi .hopf

open eq eq.ops equiv susp hopf
open [notation] sum

namespace imaginaroid

structure has_star [class] (A : Type) :=
(star : A → A)

reserve postfix `*` : (max+1)
postfix `*` := has_star.star

structure involutive_neg [class] (A : Type) extends has_neg A :=
(neg_neg : ∀a, neg (neg a) = a)

section
  variable {A : Type}
  variable [H : involutive_neg A]
  include H

  theorem neg_neg (a : A) : - -a = a := !involutive_neg.neg_neg
end

section
  /- In this section we construct, when A has a negation,
     a unit, a negation and a conjugation on susp A.
     The unit 1 is north, so south is -1.
     The negation must then swap north and south,
     while the conjugation fixes the poles and negates on meridians.
  -/
  variable {A : Type}

  definition has_one_susp [instance] : has_one (susp A) :=
  ⦃ has_one, one := north ⦄

  variable [H : has_neg A]
  include H

  definition susp_neg : susp A → susp A :=
  susp.elim south north (λa, (merid (neg a))⁻¹)

  definition has_neg_susp [instance] : has_neg (susp A) :=
  ⦃ has_neg, neg := susp_neg⦄

  definition susp_star : susp A → susp A :=
  susp.elim north south (λa, merid (neg a))

  definition has_star_susp [instance] : has_star (susp A) :=
  ⦃ has_star, star := susp_star ⦄
end

section
  -- If negation on A is involutive, so is negation on susp A
  variable {A : Type}
  variable [H : involutive_neg A]
  include H

  definition susp_neg_neg (x : susp A) : - - x = x :=
  begin
    induction x with a,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, rewrite ap_id,
      rewrite (ap_compose' (λy, -y)),
      krewrite susp.elim_merid, rewrite ap_inv,
      krewrite susp.elim_merid, rewrite neg_neg,
      rewrite inv_inv, apply hrefl }
  end

  definition involutive_neg_susp [instance] : involutive_neg (susp A) :=
  ⦃ involutive_neg, neg_neg := susp_neg_neg ⦄

  definition susp_star_star (x : susp A) : x** = x :=
  begin
    induction x with a,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, rewrite ap_id,
      krewrite (ap_compose' (λy, y*)),
      do 2 krewrite susp.elim_merid, rewrite neg_neg,
      apply hrefl }
  end

  definition susp_neg_star (x : susp A) : (-x)* = -x* :=
  begin
    induction x with a,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover,
      krewrite [ap_compose' (λy, y*),ap_compose' (λy, -y) (λy, y*)],
      do 3 krewrite susp.elim_merid, rewrite ap_inv, krewrite susp.elim_merid,
      apply hrefl }
  end
end

structure imaginaroid [class] (A : Type)
  extends involutive_neg A, has_mul (susp A) :=
(one_mul : ∀x, mul one x = x)
(mul_one : ∀x, mul x one = x)
(mul_neg : ∀x y, mul x (@susp_neg A ⦃ has_neg, neg := neg ⦄ y) =
           @susp_neg A ⦃ has_neg, neg := neg ⦄ (mul x y))
(norm : ∀x, mul x (@susp_star A ⦃ has_neg, neg := neg ⦄ x) = one)
(star_mul : ∀x y, @susp_star A ⦃ has_neg, neg := neg ⦄ (mul x y)
  = mul (@susp_star A ⦃ has_neg, neg := neg ⦄ y)
        (@susp_star A ⦃ has_neg, neg := neg ⦄ x))

section
  variable {A : Type}
  variable [H : imaginaroid A]
  include H

  theorem one_mul (x : susp A) : 1 * x = x := !imaginaroid.one_mul
  theorem mul_one (x : susp A) : x * 1 = x := !imaginaroid.mul_one
  theorem mul_neg (x y : susp A) : x * -y = -x * y := !imaginaroid.mul_neg

  /- this should not be an instance because we typically construct
     the h_space structure on susp A before defining
     the imaginaroid structure on A -/
  definition imaginaroid_h_space : h_space (susp A) :=
  ⦃ h_space, one := one, mul := mul, one_mul := one_mul, mul_one := mul_one ⦄

  theorem norm (x : susp A) : x * x* = 1 := !imaginaroid.norm
  theorem star_mul (x y : susp A) : (x * y)* = y* * x* := !imaginaroid.star_mul
  theorem one_star : 1* = 1 :> susp A := idp

  theorem neg_mul (x y : susp A) : (-x) * y = -x * y :=
  calc
    (-x) * y = ((-x) * y)**  : susp_star_star
         ... = (y* * (-x)*)* : star_mul
         ... = (y* * -x*)*   : susp_neg_star
         ... = (-y* * x*)*   : mul_neg
         ... = -(y* * x*)*   : susp_neg_star
         ... = -x** * y**    : star_mul
         ... = -x * y**      : susp_star_star
         ... = -x * y        : susp_star_star

  theorem norm' (x : susp A) : x* * x = 1 :=
  calc
    x* * x = (x* * x)**  : susp_star_star
       ... = (x* * x**)* : star_mul
       ... = 1*          : norm
       ... = 1           : one_star
end

/- Here we prove that if A has an associative imaginaroid structure,
   then join (susp A) (susp A) gets an h_space structure -/
section
  parameter A : Type
  parameter [H : imaginaroid A]
  parameter (assoc : Πa b c : susp A, (a * b) * c = a * b * c)
  include A H assoc

  open join

  section lemmata
    parameters (a b c d : susp A)

    local abbreviation f : susp A → susp A :=
    λx, a * c * (-x)

    local abbreviation g : susp A → susp A :=
    λy, c * y * b

    definition lemma_1 : f (-1) = a * c :=
    calc
      a * c * (- -1) = a * c * 1  : idp
                 ... = a * c      : mul_one

    definition lemma_2 : f (c* * a* * d * b*) = - d * b* :=
    calc
      a * c * (-c* * a* * d * b*)
        = a * (-c * c* * a* * d * b*)     : mul_neg
    ... = -a * c * c* * a* * d * b*       : mul_neg
    ... = -(a * c) * c* * a* * d * b*     : assoc
    ... = -((a * c) * c*) * a* * d * b*   : assoc
    ... = -(a * c * c*) * a* * d * b*     : assoc
    ... = -(a * 1) * a* * d * b*          : norm
    ... = -a * a* * d * b*                : mul_one
    ... = -(a * a*) * d * b*              : assoc
    ... = -1 * d * b*                     : norm
    ... = -d * b*                         : one_mul

    definition lemma_3 : g 1 = c * b :=
    calc
      c * 1 * b = c * b : one_mul

    definition lemma_4 : g (c* * a* * d * b*) = a* * d :=
    calc
      c * (c* * a* * d * b*) * b
        = (c * c* * a* * d * b*) * b      : assoc
    ... = ((c * c*) * a* * d * b*) * b    : assoc
    ... = (1 * a* * d * b*) * b           : norm
    ... = (a* * d * b*) * b               : one_mul
    ... = a* * (d * b*) * b               : assoc
    ... = a* * d * b* * b                 : assoc
    ... = a* * d * 1                      : norm'
    ... = a* * d                          : mul_one
  end lemmata

  /-
    in the algebraic form, the Cayley-Dickson multiplication has:

      (a,b) * (c,d) = (a * c - d * b*, a* * d + c * b)

    here we do the spherical form.
  -/
  definition cd_mul (x y : join (susp A) (susp A)) : join (susp A) (susp A) :=
  begin
    induction x with a b a b,
    { induction y with c d c d,
      { exact inl (a * c) },
      { exact inr (a* * d) },
      { apply glue }
    },
    { induction y with c d c d,
      { exact inr (c * b) },
      { exact inl (- d * b*) },
      { apply inverse, apply glue }
    },
    { induction y with c d c d,
      { apply glue },
      { apply inverse, apply glue },
      { apply eq_pathover,
        krewrite [join.elim_glue,join.elim_glue],
        change join.diamond (a * c) (-d * b*) (c * b) (a* * d),
        rewrite [-(lemma_1 a c),-(lemma_2 a b c d),
                 -(lemma_3 b c),-(lemma_4 a b c d)],
        apply join.ap_diamond (f a c) (g b c),
        generalize (c* * a* * d * b*), clear a b c d,
        intro x, induction x with i,
        { apply join.vdiamond, reflexivity },
        { apply join.hdiamond, reflexivity },
        { apply join.twist_diamond } } }
  end

  definition cd_one_mul (x : join (susp A) (susp A)) : cd_mul (inl 1) x = x :=
  begin
    induction x with a b a b,
    { apply ap inl, apply one_mul },
    { apply ap inr, apply one_mul },
    { apply eq_pathover, rewrite ap_id, unfold cd_mul, krewrite join.elim_glue,
      apply join.hsquare }
  end

  definition cd_mul_one (x : join (susp A) (susp A)) : cd_mul x (inl 1) = x :=
  begin
    induction x with a b a b,
    { apply ap inl, apply mul_one },
    { apply ap inr, apply one_mul },
    { apply eq_pathover, rewrite ap_id, unfold cd_mul, krewrite join.elim_glue,
      apply join.hsquare }
  end

  definition cd_h_space [instance] : h_space (join (susp A) (susp A)) :=
  ⦃ h_space, one := inl one, mul := cd_mul,
    one_mul := cd_one_mul, mul_one := cd_mul_one ⦄

end

end imaginaroid
