/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jakob von Raumer

The Rezk completion
-/

import algebra.category hit.two_quotient types.trunc types.arrow algebra.category.functor.attributes

open eq category equiv trunc_two_quotient is_trunc iso e_closure function pi trunctype

namespace rezk
  section
  
  universes l k
  parameters {A : Type.{l}} [C : precategory.{l k} A]
  include C

  inductive rezk_Q : Π ⦃a b : A⦄, e_closure iso a b → e_closure iso a b → Type :=
  | comp_con : Π ⦃a b c : A⦄ (g : b ≅ c) (f : a ≅ b) , rezk_Q [f ⬝i g] ([f] ⬝r [g])

  definition rezk_carrier := trunc_two_quotient 1 iso rezk_Q

  local attribute rezk_carrier [reducible]
  definition is_trunc_rezk_carrier [instance] : is_trunc 1 rezk_carrier := _

  variables {a b c : A}
  definition elt (a : A) : rezk_carrier := incl0 a
  definition pth (f : a ≅ b) : elt a = elt b := incl1 f

  definition resp_comp (g : b ≅ c) (f : a ≅ b) : pth (f ⬝i g) = pth f ⬝ pth g :=
  incl2 (rezk_Q.comp_con g f)

  definition resp_id (a : A) : pth (iso.refl a) = idp :=
  begin
    apply cancel_right (pth (iso.refl a)), refine _ ⬝ !idp_con⁻¹,
    refine !resp_comp⁻¹ ⬝ _,
    apply ap pth, apply iso_eq, apply id_left,
  end

  protected definition rec {P : rezk_carrier → Type} [Π x, is_trunc 1 (P x)]
    (Pe : Π a, P (elt a)) (Pp : Π ⦃a b⦄ (f : a ≅ b), Pe a =[pth f] Pe b)
    (Pcomp : Π ⦃a b c⦄ (g : b ≅ c) (f : a ≅ b),
      change_path (resp_comp g f) (Pp (f ⬝i g)) = Pp f ⬝o Pp g)
    (x : rezk_carrier) : P x :=
  begin
    induction x,
    { apply Pe },
    { apply Pp },
    { induction q with a b c g f, apply Pcomp }
  end

  protected definition rec_on {P : rezk_carrier → Type} [Π x, is_trunc 1 (P x)]
    (x : rezk_carrier)
    (Pe : Π a, P (elt a)) (Pp : Π ⦃a b⦄ (f : a ≅ b), Pe a =[pth f] Pe b)
    (Pcomp : Π ⦃a b c⦄ (g : b ≅ c) (f : a ≅ b),
      change_path (resp_comp g f) (Pp (f ⬝i g)) = Pp f ⬝o Pp g) : P x :=
  rec Pe Pp Pcomp x  

  protected definition set_rec {P : rezk_carrier → Type} [Π x, is_set (P x)]
    (Pe : Π a, P (elt a)) (Pp : Π⦃a b⦄ (f : a ≅ b), Pe a =[pth f] Pe b)
    (x : rezk_carrier) : P x :=
  rec Pe Pp !center x

  protected definition prop_rec {P : rezk_carrier → Type} [Π x, is_prop (P x)]
    (Pe : Π a, P (elt a)) (x : rezk_carrier) : P x :=
  rec Pe !center !center x

  protected definition elim {P : Type} [is_trunc 1 P] (Pe : A → P) 
    (Pp : Π ⦃a b⦄ (f : a ≅ b), Pe a = Pe b)
    (Pcomp : Π ⦃a b c⦄ (g : b ≅ c) (f : a ≅ b), Pp (f ⬝i g) = Pp f ⬝ Pp g)
    (x : rezk_carrier) : P :=
  begin
    induction x,
    { exact Pe a },
    { exact Pp s },
    { induction q with a b c g f, exact Pcomp g f }
  end

  protected definition elim_on [reducible] {P : Type} [is_trunc 1 P] (x : rezk_carrier) 
    (Pe : A → P) (Pp : Π ⦃a b⦄ (f : a ≅ b), Pe a = Pe b)
    (Pcomp : Π ⦃a b c⦄ (g : b ≅ c) (f : a ≅ b), Pp (f ⬝i g) = Pp f ⬝ Pp g) : P :=
  elim Pe Pp Pcomp x

  protected definition set_elim [reducible] {P : Type} [is_set P] (Pe : A → P)
    (Pp : Π ⦃a b⦄ (f : a ≅ b), Pe a = Pe b) (x : rezk_carrier) : P :=
  elim Pe Pp !center x

  protected definition prop_elim [reducible] {P : Type} [is_prop P] (Pe : A → P)
    (x : rezk_carrier) : P :=
  elim Pe !center !center x

  definition elim_pth {P : Type} [is_trunc 1 P] {Pe : A → P} {Pp : Π⦃a b⦄ (f : a ≅ b), Pe a = Pe b}
    (Pcomp : Π⦃a b c⦄ (g : b ≅  c) (f : a ≅ b), Pp (f ⬝i g) = Pp f ⬝ Pp g) {a b : A} (f : a ≅ b) :
    ap (elim Pe Pp Pcomp) (pth f) = Pp f :=
  !elim_incl1

  --TODO generalize this to arbitrary truncated two-quotients or not?
  protected definition elim_set.{m} [reducible] (Pe : A → Set.{m}) (Pp : Π ⦃a b⦄ (f : a ≅ b), Pe a ≃ Pe b)
    (Pcomp : Π ⦃a b c⦄ (g : b ≅ c) (f : a ≅ b) (x : Pe a), Pp (f ⬝i g) x = Pp g (Pp f x))
    (x : rezk_carrier) : Set.{m} :=
  elim Pe (λa b f, tua (Pp f)) (λa b c g f, ap tua (equiv_eq (Pcomp g f)) ⬝ !tua_trans) x

  protected definition elim_set_pt.{m} [reducible] (Pe : A → Set.{m}) (Pp : Π ⦃a b⦄ (f : a ≅ b), Pe a ≃ Pe b)
    (Pcomp : Π ⦃a b c⦄ (g : b ≅ c) (f : a ≅ b) (x : Pe a), Pp (f ⬝i g) x = Pp g (Pp f x))
    (a : A) : trunctype.carrier (rezk.elim_set Pe Pp Pcomp (elt a)) = Pe a :=
  idp

  protected theorem elim_set_pth {Pe : A → Set} {Pp : Π⦃a b⦄ (f : a ≅ b), Pe a ≃ Pe b}
    (Pcomp : Π⦃a b c⦄ (g : b ≅ c) (f : a ≅ b) (x : Pe a), Pp (f ⬝i g) x = Pp g (Pp f x))
    {a b : A} (f : a ≅ b) :
    transport (elim_set Pe Pp Pcomp) (pth f) = Pp f :=
  begin
    rewrite [tr_eq_cast_ap_fn, ↑elim_set, ▸*],
    rewrite [ap_compose' trunctype.carrier, elim_pth], apply tcast_tua_fn
  end

  end
end rezk open rezk

attribute rezk.elt [constructor]
attribute rezk.rec rezk.elim [unfold 8] [recursor 8]
attribute rezk.rec_on rezk.elim_on [unfold 5]
attribute rezk.set_rec rezk.set_elim [unfold 7]
attribute rezk.prop_rec rezk.prop_elim
          rezk.elim_set [unfold 6]

namespace rezk
  section
  universes l k
  parameters (A : Type.{l}) (C : precategory.{l k} A)

  definition rezk_hom_left_pt [constructor] (a : A) (b : @rezk_carrier A C) : Set.{k} :=
  begin
    refine rezk.elim_set _ _ _ b,
    { clear b, intro b, exact trunctype.mk' 0 (hom a b) },
    { clear b, intro b b' f, apply equiv_postcompose (iso.to_hom f) },
    { clear b, intro b b' b'' f g x, apply !assoc⁻¹ }
  end

  private definition pathover_rezk_hom_left_pt {a b c : A} (f : hom a b) (g : b ≅ c) :
    pathover (rezk_hom_left_pt a) f (pth g) ((to_hom g) ∘ f) :=
  begin
    apply pathover_of_tr_eq, apply @homotopy_of_eq _ _ _ (λ f, (to_hom g) ∘ f),
    apply rezk.elim_set_pth,
  end

  definition rezk_hom_left_pth_1_trunc [instance] (a a' : A) (f : a ≅ a') :
    Π b, is_trunc 1 (carrier (rezk_hom_left_pt a b) ≃ carrier (rezk_hom_left_pt a' b)) :=
  λ b, is_trunc_equiv _ _ _

  definition rezk_hom_left_pth (a a' : A) (f : a ≅ a') (b : rezk_carrier) :
    carrier (rezk_hom_left_pt a b) ≃ carrier (rezk_hom_left_pt a' b) :=
  begin
    --induction b using rezk.rec with b' b' b g, --why does this not work if it works below?
    refine @rezk.rec _ _ _ (rezk_hom_left_pth_1_trunc a a' f) _ _ _ b,
    intro b, apply equiv_precompose (to_hom f⁻¹ⁱ), --how do i unfold properly at this point?
    { intro b b' g, apply equiv_pathover, intro g' g'' H, 
      refine !pathover_rezk_hom_left_pt ⬝op _,
      refine !assoc ⬝ ap (λ x, x ∘ _) _,  refine eq_of_parallel_po_right _ H, 
      apply pathover_rezk_hom_left_pt },
    intro b b' b'' g g', apply @is_prop.elim, apply is_trunc_pathover, apply is_trunc_equiv
  end

  definition rezk_hom [unfold 3 4] (a b : @rezk_carrier A C) : Set.{k} :=
  begin
    refine rezk.elim_set _ _ _ a,
    { clear a, intro a, exact rezk_hom_left_pt a b },
    { clear a, intro a a' f, apply rezk_hom_left_pth a a' f },
    { clear a, intro a a' a'' Ef Eg Rfg, induction b using rezk.rec,
      apply assoc, apply is_prop.elimo, apply is_set.elimo }
  end

  private definition pathover_rezk_hom_left {a b c : A} (f : hom a c) (g : a ≅ b) :
    pathover (λ x, rezk_hom x (elt c)) f (pth g) (f ∘ (to_hom g)⁻¹) :=
  begin
    apply pathover_of_tr_eq, apply @homotopy_of_eq _ _ _ (λ f, f ∘ (to_hom g)⁻¹),
    apply rezk.elim_set_pth,
  end

  private definition pathover_rezk_hom_right {a b c : A} (f : hom a b) (g : b ≅ c) : --todo delete?
    pathover (rezk_hom (elt a)) f (pth g) ((to_hom g) ∘ f) :=
  begin
    apply pathover_rezk_hom_left_pt,
  end

  private definition transport_rezk_hom_eq_comp {a c : A} (f : hom a a) (g : a ≅ c) :
    transport (λ x, rezk_hom x x) (pth g) f = (to_hom g) ∘ f ∘ (to_hom g)⁻¹ :=
  begin
    apply concat, apply tr_diag_eq_tr_tr rezk_hom,
    apply concat, apply ap (λ x, _ ▸ x),
     apply tr_eq_of_pathover, apply pathover_rezk_hom_left,
    apply tr_eq_of_pathover, apply pathover_rezk_hom_left_pt
  end

  definition rezk_id (a : @rezk_carrier A C) : rezk_hom a a :=
  begin
    induction a using rezk.rec,
    apply id,
    { apply pathover_of_tr_eq, refine !transport_rezk_hom_eq_comp ⬝ _,
      refine (ap (λ x, to_hom f ∘ x) !id_left) ⬝ _, apply right_inverse },
    apply is_set.elimo
  end

  definition rezk_comp_pt_pt [reducible] {c : rezk_carrier} {a b : A}
    (g : carrier (rezk_hom (elt b) c))
    (f : carrier (rezk_hom (elt a) (elt b))) : carrier (rezk_hom (elt a) c) :=
  begin
    induction c using rezk.set_rec with c c c' ic,
    exact g ∘ f,
    { apply arrow_pathover_left, intro d,
      apply concato !pathover_rezk_hom_left_pt, apply pathover_idp_of_eq, 
      apply concat, apply assoc, apply ap (λ x, x ∘ f), 
      apply inverse, apply tr_eq_of_pathover, apply pathover_rezk_hom_left_pt },
  end

  definition rezk_comp_pt_pth [reducible] {c : rezk_carrier} {a b b' : A} {ib : iso b b'} :
    pathover (λ b, carrier (rezk_hom b c) → carrier (rezk_hom (elt a) b) → carrier (rezk_hom (elt a) c))
      (λ g f, rezk_comp_pt_pt g f) (pth ib) (λ g f, rezk_comp_pt_pt g f) :=
  begin
    apply arrow_pathover_left, intro x,
    apply arrow_pathover_left, intro y,
    induction c using rezk.set_rec with c c c' ic,
    {  apply pathover_of_eq, apply inverse, 
      apply concat, apply ap (λ x, rezk_comp_pt_pt x _), apply tr_eq_of_pathover,
       apply pathover_rezk_hom_left,
      apply concat, apply ap (rezk_comp_pt_pt _), apply tr_eq_of_pathover,
       apply pathover_rezk_hom_left_pt,
      refine !assoc ⬝ ap (λ x, x ∘ y) _, 
      refine !assoc⁻¹ ⬝ _, 
      refine ap (λ y, x ∘ y) !iso.left_inverse ⬝ _,
      apply id_right },
    apply @is_prop.elimo
  end

  definition rezk_comp {a b c : @rezk_carrier A C} (g : rezk_hom b c) (f : rezk_hom a b) :
    rezk_hom a c :=
  begin
    induction a using rezk.set_rec with a a a' ia,
    { induction b using rezk.set_rec with b b b' ib,
      apply rezk_comp_pt_pt g f, apply rezk_comp_pt_pth },
    { induction b using rezk.set_rec with b b b' ib, 
      apply arrow_pathover_left, intro f, 
      induction c using rezk.set_rec with c c c' ic,
      { apply concato, apply pathover_rezk_hom_left,
        apply pathover_idp_of_eq, refine !assoc⁻¹ ⬝ ap (λ x, g ∘ x) _⁻¹,
        apply tr_eq_of_pathover, apply pathover_rezk_hom_left },
      apply is_prop.elimo,
      apply is_prop.elimo }
  end

  definition is_set_rezk_hom [instance] (a b : @rezk_carrier A C) : is_set (rezk_hom a b) :=
  _

  protected definition id_left {a b : @rezk_carrier A C} (f : rezk_hom a b) :
    rezk_comp (rezk_id b) f = f :=
  begin
    induction a using rezk.prop_rec with a a a' ia,
    induction b using rezk.prop_rec with b b b' ib,
    apply id_left,
  end

  protected definition id_right {a b : @rezk_carrier A C} (f : rezk_hom a b) :
    rezk_comp f (rezk_id a) = f :=
  begin
    induction a using rezk.prop_rec with a a a' ia,
    induction b using rezk.prop_rec with b b b' ib,
    apply id_right,
  end

  protected definition assoc {a b c d : @rezk_carrier A C} (h : rezk_hom c d)
    (g : rezk_hom b c) (f : rezk_hom a b) :
    rezk_comp h (rezk_comp g f) = rezk_comp (rezk_comp h g) f :=
  begin
    induction a using rezk.prop_rec with a a a' ia,
    induction b using rezk.prop_rec with b b b' ib,
    induction c using rezk.prop_rec with c c c' ic,
    induction d using rezk.prop_rec with d d d' id,
    apply assoc,
  end

  definition rezk_precategory [instance] : precategory (@rezk_carrier A C) :=
  precategory.mk rezk_hom @rezk_comp rezk_id @assoc @id_left @id_right

  end

  definition to_rezk_Precategory.{l k} : Precategory.{l k} → Precategory.{(max l k) k} :=
  begin
    intro C, apply Precategory.mk (@rezk_carrier (Precategory.carrier C) C),
    apply rezk_precategory _ _,
  end
  
  definition rezk_functor [constructor] (C : Precategory) : functor C (to_rezk_Precategory C) :=
  begin
    fapply functor.mk, apply elt,
    { intro a b f, exact f },
    do 2 (intros; reflexivity)
  end

  section
  parameters {A : Type} [C : precategory A]
  include C

  protected definition elt_iso_of_iso [reducible] {a b : A} (f : a ≅ b) : elt a ≅ elt b :=
  begin
    fapply iso.mk, apply to_hom f, apply functor.preserve_is_iso (rezk_functor _)
  end

  protected definition iso_of_elt_iso [reducible] {a b : A} (f : elt a ≅ elt b) : a ≅ b :=
  begin
    cases f with f Hf, cases Hf with inv linv rinv,
    fapply iso.mk, exact f, fapply is_iso.mk, exact inv, exact linv, exact rinv
  end

  protected definition iso_of_elt_iso_distrib {a b c : A} (f : elt a ≅ elt b) (g : elt b ≅ elt c) :
    iso_of_elt_iso (f ⬝i g) = (iso_of_elt_iso f) ⬝i (iso_of_elt_iso g) :=
  begin
    cases g with g Hg, cases Hg with invg linvg rinvg,
    cases f with f Hf, cases Hf with invf linvf rinvf,
    reflexivity
  end

  protected definition iso_equiv_elt_iso (a b : A) : (a ≅ b) ≃ (elt a ≅ elt b) :=
  begin
    fapply equiv.MK, apply elt_iso_of_iso, apply iso_of_elt_iso,
    { intro f, cases f with f Hf, cases Hf with inv linv rinv, fapply iso_eq, reflexivity },
    { intro f, fapply iso_eq, reflexivity }
  end

  private definition hom_transport_eq_transport_hom {a b b' : @rezk_carrier A C} (f : a ≅ b)
    (p : b = b') : to_hom (transport (iso a) p f) = transport (λ x, hom _ _) p (to_hom f) :=
  by cases p; reflexivity

  private definition hom_transport_eq_transport_hom' {a a' b : @rezk_carrier A C} (f : a ≅ b)
    (p : a = a') : to_hom (transport (λ x, iso x b) p f) = transport (λ x, hom _ _) p (to_hom f) :=
  by cases p; reflexivity

  private definition pathover_iso_pth {a b b' : A} (f : elt a ≅ elt b) 
    (ib : b ≅ b') : pathover (λ x, iso (elt a) x) f (pth ib) (f ⬝i elt_iso_of_iso ib) :=
  begin
    apply pathover_of_tr_eq, apply iso_eq,
    apply concat, apply hom_transport_eq_transport_hom,
    apply tr_eq_of_pathover, apply pathover_rezk_hom_right A C
  end

  private definition pathover_iso_pth' {a a' b : A} (f : elt a ≅ elt b)
    (ia : a ≅ a') : pathover (λ x, iso x (elt b)) f (pth ia) (elt_iso_of_iso (iso.symm ia) ⬝i f) :=
  begin
    apply pathover_of_tr_eq, apply iso_eq,
    apply concat, apply hom_transport_eq_transport_hom',
    apply tr_eq_of_pathover, apply pathover_rezk_hom_left A C
  end

  private definition eq_of_iso_pt {a : A} {b : @rezk_carrier A C} :
    elt a ≅ b → elt a = b :=
  begin
    intro f,
    induction b using rezk.set_rec with b b b' ib,
    apply pth, apply iso_of_elt_iso f,
    apply arrow_pathover, intro f g p, apply eq_pathover,
    refine !ap_constant ⬝ph _ ⬝hp !ap_id⁻¹, apply square_of_eq,
    refine !resp_comp⁻¹ ⬝ (ap pth _)⁻¹ ⬝ !idp_con⁻¹, 
    apply concat, apply inverse, apply ap rezk.iso_of_elt_iso, 
    apply eq_of_parallel_po_right (pathover_iso_pth _ _) p, 
    apply concat, apply iso_of_elt_iso_distrib,
    apply ap (λ x, _ ⬝i x), apply equiv.to_left_inv !iso_equiv_elt_iso
  end

  protected definition eq_of_iso {a b : @rezk_carrier A C} :
    a ≅ b → a = b :=
  begin
    intro f,
    induction a using rezk.set_rec with a a a' ia,
    apply eq_of_iso_pt f,
    { induction b using rezk.set_rec with b b b' ib,
      { apply arrow_pathover, intro f g p, apply eq_pathover,
        refine !ap_id ⬝ph _ ⬝hp !ap_constant⁻¹, apply square_of_eq,
        refine (ap pth _) ⬝ !resp_comp, 
        assert H : g = (elt_iso_of_iso (iso.symm ia) ⬝i f),
        apply eq_of_parallel_po_right p (pathover_iso_pth' _ _),
        rewrite H, apply inverse, 
        apply concat, apply ap (λ x, ia ⬝i x), apply iso_of_elt_iso_distrib,
        apply concat, apply ap (λ x, _ ⬝i (x ⬝i _)), apply equiv.to_left_inv !iso_equiv_elt_iso, 
        apply iso_eq, apply inverse_comp_cancel_right },
       apply @is_prop.elimo }
  end

  protected definition eq_of_iso_of_eq (a b : @rezk_carrier A C) (p : a = b) :
    eq_of_iso (iso_of_eq p) = p :=
  begin
    cases p, clear b,
    induction a using rezk.prop_rec,
    refine ap pth _ ⬝ !resp_id,
    apply iso_eq, reflexivity
  end

  protected definition iso_of_eq_of_iso (a b : @rezk_carrier A C) (f : a ≅ b) :
    iso_of_eq (eq_of_iso f) = f :=
  begin
    induction a using rezk.prop_rec with a,
    induction b using rezk.prop_rec with b,
    cases f with f Hf, apply iso_eq,
    apply concat, apply ap to_hom, apply !transport_iso_of_eq⁻¹,
    apply concat, apply ap to_hom, apply tr_eq_of_pathover, apply pathover_iso_pth,
    cases Hf with invf linv rinv, apply id_right,
  end

  end

  definition rezk_category.{l k} {A : Type.{l}} [C : precategory.{l k} A] :
    category.{(max l k) k} (@rezk_carrier.{l k} A C) :=
  begin
    fapply category.mk (rezk_precategory A C),
    intros, fapply is_equiv.adjointify,
    apply rezk.eq_of_iso,
    apply rezk.iso_of_eq_of_iso,
    apply rezk.eq_of_iso_of_eq
  end

  section
  variable (C : Precategory)

  definition fully_faithful_rezk_functor : fully_faithful (rezk_functor C) :=
  by intros; apply is_equiv.is_equiv_id

  open trunc
  definition essentially_surj_rezk_functor : essentially_surjective (rezk_functor C) :=
  begin
    intro a, esimp[to_rezk_Precategory] at *,
    induction a using rezk.prop_rec with a, apply tr,
    constructor, apply iso.refl (elt a),
  end

  definition is_weak_equiv_rezk_functor : is_weak_equivalence (rezk_functor C) :=
  prod.mk (fully_faithful_rezk_functor C) (essentially_surj_rezk_functor C)

  end
  
end rezk
