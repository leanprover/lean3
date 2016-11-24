/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

The Cofiber Type
-/
import hit.pushout function .susp types.unit

open eq pushout unit pointed is_trunc is_equiv susp unit equiv

definition cofiber {A B : Type} (f : A → B) := pushout (λ (a : A), ⋆) f

namespace cofiber
  section
  parameters {A B : Type} (f : A → B)

  protected definition base : cofiber f := inl ⋆

  protected definition cod : B → cofiber f := inr

  parameter {f}
  protected definition glue (a : A) : cofiber.base f = cofiber.cod f (f a) :=
  pushout.glue a

  parameter (f)
  protected definition contr_of_equiv [H : is_equiv f] : is_contr (cofiber f) :=
  begin
    fapply is_contr.mk, exact base,
    intro a, induction a with [u, b],
    { cases u, reflexivity },
    { exact !glue ⬝ ap inr (right_inv f b) },
    { apply eq_pathover, refine _ ⬝hp !ap_id⁻¹, refine !ap_constant ⬝ph _,
      apply move_bot_of_left, refine !idp_con ⬝ph _, apply transpose, esimp,
      refine _ ⬝hp (ap (ap inr) !adj⁻¹), refine _ ⬝hp !ap_compose, apply square_Flr_idp_ap },
  end

  parameter {f}
  protected definition rec {P : cofiber f → Type}
    (Pbase : P base) (Pcod : Π (b : B), P (cod b))
    (Pglue : Π (a : A), pathover P Pbase (glue a) (Pcod (f a))) :
    (Π y, P y) :=
  begin
    intro y, induction y, induction x, exact Pbase, exact Pcod x, esimp, exact Pglue x,
  end

  protected definition rec_on {P : cofiber f → Type} (y : cofiber f)
    (Pbase : P base) (Pcod : Π (b : B), P (cod b))
    (Pglue : Π (a : A), pathover P Pbase (glue a) (Pcod (f a))) : P y :=
  cofiber.rec Pbase Pcod Pglue y

  protected definition elim {P : Type} (Pbase : P) (Pcod : B → P)
    (Pglue : Π (x : A), Pbase = Pcod (f x)) (y : cofiber f) : P :=
  pushout.elim (λu, Pbase) Pcod Pglue y

  protected definition elim_on {P : Type} (y : cofiber f) (Pbase : P) (Pcod : B → P)
    (Pglue : Π (x : A), Pbase = Pcod (f x)) : P :=
  cofiber.elim Pbase Pcod Pglue y

  protected theorem elim_glue {P : Type} (y : cofiber f) (Pbase : P) (Pcod : B → P)
    (Pglue : Π (x : A), Pbase = Pcod (f x)) (a : A)
    : ap (elim Pbase Pcod Pglue) (glue a) = Pglue a :=
  !pushout.elim_glue

  end
end cofiber

attribute cofiber.base cofiber.cod [constructor]
attribute cofiber.rec cofiber.elim [recursor 8] [unfold 8]
attribute cofiber.rec_on cofiber.elim_on [unfold 5]

-- pointed version

definition pcofiber [constructor] {A B : Type*} (f : A →* B) : Type* :=
pointed.MK (cofiber f) !cofiber.base

namespace cofiber

  variables (A : Type*)

  definition cofiber_unit : pcofiber (pconst A punit) ≃* psusp A :=
  begin
    fapply pequiv_of_pmap,
    { fconstructor, intro x, induction x, exact north, exact south, exact merid x,
      reflexivity },
    { esimp, fapply adjointify,
      { intro s, induction s, exact inl ⋆, exact inr ⋆, apply glue a },
      { intro s, induction s, do 2 reflexivity, esimp,
        apply eq_pathover, refine _ ⬝hp !ap_id⁻¹, apply hdeg_square,
        refine !(ap_compose (pushout.elim _ _ _)) ⬝ _,
        refine ap _ !elim_merid ⬝ _, apply elim_glue },
      { intro c, induction c with s, reflexivity,
        induction s, reflexivity, esimp, apply eq_pathover, apply hdeg_square,
        refine _ ⬝ !ap_id⁻¹, refine !(ap_compose (pushout.elim _ _ _)) ⬝ _,
        refine ap02 _ !elim_glue ⬝ _, apply elim_merid }},
  end

end cofiber
