/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

The Smash Product of Types.

One definition is the cofiber of the map
    wedge A B → A × B
However, we define it (equivalently) as the pushout of the maps A + B → 2 and A + B → A × B.
-/

import homotopy.circle homotopy.join types.pointed homotopy.cofiber homotopy.wedge

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge

namespace smash

  variables {A B : Type*}

  section
  open pushout

  definition prod_of_sum [unfold 3] (u : A + B) : A × B :=
  by induction u with a b; exact (a, pt); exact (pt, b)

  definition bool_of_sum [unfold 3] (u : A + B) : bool :=
  by induction u; exact ff; exact tt

  definition smash' (A B : Type*) : Type := pushout (@prod_of_sum A B) (@bool_of_sum A B)
  protected definition mk (a : A) (b : B) : smash' A B := inl (a, b)

  definition pointed_smash' [instance] [constructor] (A B : Type*) : pointed (smash' A B) :=
  pointed.mk (smash.mk pt pt)
  definition smash [constructor] (A B : Type*) : Type* :=
  pointed.mk' (smash' A B)

  definition auxl : smash A B := inr ff
  definition auxr : smash A B := inr tt
  definition gluel (a : A) : smash.mk a pt = auxl :> smash A B := glue (inl a)
  definition gluer (b : B) : smash.mk pt b = auxr :> smash A B := glue (inr b)

  end

  definition gluel' (a a' : A) : smash.mk a pt = smash.mk a' pt :> smash A B :=
  gluel a ⬝ (gluel a')⁻¹
  definition gluer' (b b' : B) : smash.mk pt b = smash.mk pt b' :> smash A B :=
  gluer b ⬝ (gluer b')⁻¹
  definition glue (a : A) (b : B) : smash.mk a pt = smash.mk pt b :=
  gluel' a pt ⬝ gluer' pt b

  definition glue_pt_left (b : B) : glue (Point A) b = gluer' pt b :=
  whisker_right _ !con.right_inv ⬝ !idp_con

  definition glue_pt_right (a : A) : glue a (Point B) = gluel' a pt :=
  proof whisker_left _ !con.right_inv qed

  definition ap_mk_left {a a' : A} (p : a = a') : ap (λa, smash.mk a (Point B)) p = gluel' a a' :=
  by induction p; exact !con.right_inv⁻¹

  definition ap_mk_right {b b' : B} (p : b = b') : ap (smash.mk (Point A)) p = gluer' b b' :=
  by induction p; exact !con.right_inv⁻¹

  protected definition rec {P : smash A B → Type} (Pmk : Πa b, P (smash.mk a b))
    (Pl : P auxl) (Pr : P auxr) (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (x : smash' A B) : P x :=
  begin
    induction x with x b u,
    { induction x with a b, exact Pmk a b },
    { induction b, exact Pl, exact Pr },
    { induction u: esimp,
      { apply Pgl },
      { apply Pgr }}
  end

  -- a rec which is easier to prove, but with worse computational properties
  protected definition rec' {P : smash A B → Type} (Pmk : Πa b, P (smash.mk a b))
    (Pg : Πa b, Pmk a pt =[glue a b] Pmk pt b) (x : smash' A B) : P x :=
  begin
    induction x using smash.rec,
    { apply Pmk },
    { exact gluel pt ▸ Pmk pt pt },
    { exact gluer pt ▸ Pmk pt pt },
    { refine change_path _ (Pg a pt ⬝o !pathover_tr),
      refine whisker_right _ !glue_pt_right ⬝ _, esimp, refine !con.assoc ⬝ _,
      apply whisker_left, apply con.left_inv },
    { refine change_path _ ((Pg pt b)⁻¹ᵒ ⬝o !pathover_tr),
      refine whisker_right _ !glue_pt_left⁻² ⬝ _,
      refine whisker_right _ !inv_con_inv_right ⬝ _, refine !con.assoc ⬝ _,
      apply whisker_left, apply con.left_inv }
  end

  theorem rec_gluel {P : smash A B → Type} {Pmk : Πa b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (a : A) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  !pushout.rec_glue

  theorem rec_gluer {P : smash A B → Type} {Pmk : Πa b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (b : B) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  !pushout.rec_glue

  theorem rec_glue {P : smash A B → Type} {Pmk : Πa b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (a : A) (b : B) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (glue a b) =
      (Pgl a ⬝o (Pgl pt)⁻¹ᵒ) ⬝o (Pgr pt ⬝o (Pgr b)⁻¹ᵒ) :=
  by rewrite [↑glue, ↑gluel', ↑gluer', +apd_con, +apd_inv, +rec_gluel, +rec_gluer]

  protected definition elim {P : Type} (Pmk : Πa b, P) (Pl Pr : P)
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (x : smash' A B) : P :=
  smash.rec Pmk Pl Pr (λa, pathover_of_eq _ (Pgl a)) (λb, pathover_of_eq _ (Pgr b)) x

  -- an elim which is easier to prove, but with worse computational properties
  protected definition elim' {P : Type} (Pmk : Πa b, P) (Pg : Πa b, Pmk a pt = Pmk pt b)
    (x : smash' A B) : P :=
  smash.rec' Pmk (λa b, pathover_of_eq _ (Pg a b)) x

  theorem elim_gluel {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (a : A) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (@gluel A B a)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑smash.elim,rec_gluel],
  end

  theorem elim_gluer {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (b : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (@gluer A B b)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑smash.elim,rec_gluer],
  end

  theorem elim_glue {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (a : A) (b : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (glue a b) = (Pgl a ⬝ (Pgl pt)⁻¹) ⬝ (Pgr pt ⬝ (Pgr b)⁻¹) :=
  by rewrite [↑glue, ↑gluel', ↑gluer', +ap_con, +ap_inv, +elim_gluel, +elim_gluer]

end smash
open smash
attribute smash.mk auxl auxr [constructor]
attribute smash.rec smash.elim [unfold 9] [recursor 9]
attribute smash.rec' smash.elim' [unfold 6]

namespace smash

  variables {A B : Type*}

  definition of_smash_pbool [unfold 2] (x : smash A pbool) : A :=
  begin
    induction x,
    { induction b, exact pt, exact a },
    { exact pt },
    { exact pt },
    { reflexivity },
    { induction b: reflexivity }
  end

  definition smash_pbool_equiv [constructor] (A : Type*) : smash A pbool ≃* A :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact of_smash_pbool },
      { intro a, exact smash.mk a tt },
      { intro a, reflexivity },
      { exact abstract begin intro x, induction x using smash.rec',
        { induction b, exact (glue a tt)⁻¹, reflexivity },
        { apply eq_pathover_id_right, induction b: esimp,
          { refine ap02 _ !glue_pt_right ⬝ph _,
            refine ap_compose (λx, smash.mk x _) _ _ ⬝ph _,
            refine ap02 _ (!ap_con ⬝ (!elim_gluel ◾ (!ap_inv ⬝ !elim_gluel⁻²))) ⬝ph _,
            apply hinverse, apply square_of_eq,
            esimp, refine (!glue_pt_right ◾ !glue_pt_left)⁻¹ },
          { apply square_of_eq, refine !con.left_inv ⬝ _, esimp, symmetry,
            refine ap_compose (λx, smash.mk x _) _ _ ⬝ _,
            exact ap02 _ !elim_glue }} end end }},
    { reflexivity }
  end

end smash
