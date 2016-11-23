/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Quotients. This is a quotient without truncation for an arbitrary type-valued binary relation.
See also .set_quotient
-/

/-
  The hit quotient is primitive, declared in init.hit.
  The constructors are, given {A : Type} (R : A → A → Type),
  * class_of : A → quotient R (A implicit, R explicit)
  * eq_of_rel : Π{a a' : A}, R a a' → class_of a = class_of a' (R explicit)
-/

import arity cubical.squareover types.arrow cubical.pathover2 types.pointed

open eq equiv sigma sigma.ops pi is_trunc pointed

namespace quotient

  variables {A : Type} {R : A → A → Type}

  protected definition elim {P : Type} (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')
    (x : quotient R) : P :=
  quotient.rec Pc (λa a' H, pathover_of_eq _ (Pp H)) x

  protected definition elim_on [reducible] {P : Type} (x : quotient R)
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') : P :=
  quotient.elim Pc Pp x

  theorem elim_eq_of_rel {P : Type} (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (quotient.elim Pc Pp) (eq_of_rel R H) = Pp H :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (eq_of_rel R H)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑quotient.elim,rec_eq_of_rel],
  end

  protected definition rec_prop {A : Type} {R : A → A → Type} {P : quotient R → Type}
    [H : Πx, is_prop (P x)] (Pc : Π(a : A), P (class_of R a)) (x : quotient R) : P x :=
  quotient.rec Pc (λa a' H, !is_prop.elimo) x

  protected definition elim_prop {P : Type} [H : is_prop P] (Pc : A → P) (x : quotient R) : P :=
  quotient.elim Pc (λa a' H, !is_prop.elim) x

  protected definition elim_type (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : quotient R → Type :=
  quotient.elim Pc (λa a' H, ua (Pp H))

  protected definition elim_type_on [reducible] (x : quotient R) (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : Type :=
  quotient.elim_type Pc Pp x

  theorem elim_type_eq_of_rel_fn (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a')
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) = to_fun (Pp H) :=
  by rewrite [tr_eq_cast_ap_fn, ↑quotient.elim_type, elim_eq_of_rel]; apply cast_ua_fn

  -- rename to elim_type_eq_of_rel_fn_inv
  theorem elim_type_eq_of_rel_inv (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a')
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H)⁻¹ = to_inv (Pp H) :=
  by rewrite [tr_eq_cast_ap_fn, ↑quotient.elim_type, ap_inv, elim_eq_of_rel]; apply cast_ua_inv_fn

  -- remove '
  theorem elim_type_eq_of_rel_inv' (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (x : Pc a')
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H)⁻¹ x = to_inv (Pp H) x :=
  ap10 (elim_type_eq_of_rel_inv Pc Pp H) x

  theorem elim_type_eq_of_rel.{u} (Pc : A → Type.{u})
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (p : Pc a)
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) p = to_fun (Pp H) p :=
  ap10 (elim_type_eq_of_rel_fn Pc Pp H) p

  definition elim_type_eq_of_rel' (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (p : Pc a)
    : pathover (quotient.elim_type Pc Pp) p (eq_of_rel R H) (to_fun (Pp H) p) :=
  pathover_of_tr_eq (elim_type_eq_of_rel Pc Pp H p)

  definition elim_type_uncurried (H : Σ(Pc : A → Type),  Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a')
    : quotient R → Type :=
  quotient.elim_type H.1 H.2
end quotient

attribute quotient.rec [recursor]
attribute quotient.elim [unfold 6] [recursor 6]
attribute quotient.elim_type [unfold 5]
attribute quotient.elim_on [unfold 4]
attribute quotient.elim_type_on [unfold 3]

namespace quotient

  section
    variables {A : Type} (R : A → A → Type)

    /- The dependent universal property -/
    definition quotient_pi_equiv (C : quotient R → Type) : (Πx, C x) ≃
      (Σ(f : Π(a : A), C (class_of R a)),  Π⦃a a' : A⦄ (H : R a a'), f a =[eq_of_rel R H] f a') :=
    begin
      fapply equiv.MK,
      { intro f, exact ⟨λa, f (class_of R a), λa a' H, apd f (eq_of_rel R H)⟩},
      { intro v x, induction v with i p, induction x,
          exact (i a),
          exact (p H)},
      { intro v, induction v with i p, esimp,
        apply ap (sigma.mk i), apply eq_of_homotopy3, intro a a' H, apply rec_eq_of_rel},
      { intro f, apply eq_of_homotopy, intro x, induction x: esimp,
        apply eq_pathover_dep, esimp, rewrite rec_eq_of_rel, exact hrflo},
    end
  end

  definition pquotient [constructor] {A : Type*} (R : A → A → Type) : Type* :=
  pType.mk (quotient R) (class_of R pt)

  /- the flattening lemma -/

  namespace flattening
  section

    parameters {A : Type} (R : A → A → Type) (C : A → Type) (f : Π⦃a a'⦄, R a a' → C a ≃ C a')
    include f
    variables {a a' : A} {r : R a a'}

    local abbreviation P [unfold 5] := quotient.elim_type C f

    definition flattening_type : Type := Σa, C a
    local abbreviation X := flattening_type
    inductive flattening_rel : X → X → Type :=
    | mk : Π⦃a a' : A⦄ (r : R a a') (c : C a), flattening_rel ⟨a, c⟩ ⟨a', f r c⟩

    definition Ppt [constructor] (c : C a) : sigma P :=
    ⟨class_of R a, c⟩

    definition Peq (r : R a a') (c : C a) : Ppt c = Ppt (f r c) :=
    begin
      fapply sigma_eq: esimp,
      { apply eq_of_rel R r},
      { refine elim_type_eq_of_rel' C f r c}
    end

    definition rec {Q : sigma P → Type} (Qpt : Π{a : A} (x : C a), Q (Ppt x))
      (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c =[Peq r c] Qpt (f r c))
      (v : sigma P) : Q v :=
    begin
      induction v with q p,
      induction q,
      { exact Qpt p},
      { apply pi_pathover_left', esimp, intro c,
        refine _ ⬝op apdt Qpt (elim_type_eq_of_rel C f H c)⁻¹ᵖ,
        refine _ ⬝op (tr_compose Q Ppt _ _)⁻¹ ,
        rewrite ap_inv,
        refine pathover_cancel_right _ !tr_pathover⁻¹ᵒ,
        refine change_path _ (Qeq H c),
        symmetry, rewrite [↑[Ppt, Peq]],
        refine whisker_left _ !ap_dpair ⬝ _,
        refine !dpair_eq_dpair_con⁻¹ ⬝ _, esimp,
        apply ap (dpair_eq_dpair _),
        esimp [elim_type_eq_of_rel',pathover_idp_of_eq],
        exact !pathover_of_tr_eq_eq_concato⁻¹},
    end

    definition elim {Q : Type} (Qpt : Π{a : A}, C a → Q)
      (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c = Qpt (f r c))
      (v : sigma P) : Q :=
    begin
      induction v with q p,
      induction q,
      { exact Qpt p},
      { apply arrow_pathover_constant_right, esimp,
        intro c, exact Qeq H c ⬝ ap Qpt (elim_type_eq_of_rel C f H c)⁻¹},
    end

    theorem elim_Peq {Q : Type} (Qpt : Π{a : A}, C a → Q)
      (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c = Qpt (f r c)) {a a' : A} (r : R a a')
      (c : C a) : ap (elim @Qpt Qeq) (Peq r c) = Qeq r c :=
    begin
      refine !ap_dpair_eq_dpair ⬝ _,
      refine !apd011_eq_apo11_apd ⬝ _,
      rewrite [rec_eq_of_rel, ▸*],
      refine !apo11_arrow_pathover_constant_right ⬝ _,
      rewrite [↑elim_type_eq_of_rel', to_right_inv !pathover_equiv_tr_eq, ap_inv],
      apply inv_con_cancel_right
    end

    open flattening_rel
    definition flattening_lemma : sigma P ≃ quotient flattening_rel :=
    begin
      fapply equiv.MK,
      { refine elim _ _,
        { intro a c, exact class_of _ ⟨a, c⟩},
        { intro a a' r c, apply eq_of_rel, constructor}},
      { intro q, induction q with x x x' H,
        { exact Ppt x.2},
        { induction H, esimp, apply Peq}},
      { intro q, induction q with x x x' H: esimp,
        { induction x with a c, reflexivity},
        { induction H, esimp, apply eq_pathover, apply hdeg_square,
          refine ap_compose (elim _ _) (quotient.elim _ _) _ ⬝ _,
          rewrite [elim_eq_of_rel, ap_id, ▸*],
          apply elim_Peq}},
      { refine rec (λa x, idp) _, intros,
        apply eq_pathover, apply hdeg_square,
          refine ap_compose (quotient.elim _ _) (elim _ _) _ ⬝ _,
          rewrite [elim_Peq, ap_id, ▸*],
          apply elim_eq_of_rel}
    end

  end
  end flattening

  section
  open is_equiv equiv prod prod.ops
  variables {A : Type} (R : A → A → Type)
             {B : Type} (Q : B → B → Type)
             (f : A → B) (k : Πa a' : A, R a a' → Q (f a) (f a'))
  include f k

  protected definition functor [reducible] : quotient R → quotient Q :=
  quotient.elim (λa, class_of Q (f a)) (λa a' r, eq_of_rel Q (k a a' r))

  variables [F : is_equiv f] [K : Πa a', is_equiv (k a a')]
  include F K

  protected definition functor_inv [reducible] : quotient Q → quotient R :=
  quotient.elim (λb, class_of R (f⁻¹ b))
                (λb b' q, eq_of_rel R ((k (f⁻¹ b) (f⁻¹ b'))⁻¹
                          ((right_inv f b)⁻¹ ▸ (right_inv f b')⁻¹ ▸ q)))

  protected definition is_equiv [instance]
    : is_equiv (quotient.functor R Q f k):=
  begin
    fapply adjointify _ (quotient.functor_inv R Q f k),
    { intro qb, induction qb with b b b' q,
      { apply ap (class_of Q), apply right_inv },
      { apply eq_pathover, rewrite [ap_id,ap_compose' (quotient.elim _ _)],
        do 2 krewrite elim_eq_of_rel, rewrite (right_inv (k (f⁻¹ b) (f⁻¹ b'))),
        have H1 : pathover (λz : B × B, Q z.1 z.2)
          ((right_inv f b)⁻¹ ▸ (right_inv f b')⁻¹ ▸ q)
          (prod_eq (right_inv f b) (right_inv f b')) q,
        begin apply pathover_of_eq_tr, krewrite [prod_eq_inv,prod_eq_transport] end,
        have H2 : square
          (ap (λx : (Σz : B × B, Q z.1 z.2), class_of Q x.1.1)
            (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1))
          (ap (λx : (Σz : B × B, Q z.1 z.2), class_of Q x.1.2)
            (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1))
          (eq_of_rel Q ((right_inv f b)⁻¹ ▸ (right_inv f b')⁻¹ ▸ q))
          (eq_of_rel Q q),
        from
          natural_square_tr (λw : (Σz : B × B, Q z.1 z.2), eq_of_rel Q w.2)
          (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1),
        krewrite (ap_compose' (class_of Q)) at H2,
        krewrite (ap_compose' (λz : B × B, z.1)) at H2,
        rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
        krewrite prod.ap_pr1 at H2, krewrite prod_eq_pr1 at H2,
        krewrite (ap_compose' (class_of Q) (λx : (Σz : B × B, Q z.1 z.2), x.1.2)) at H2,
        krewrite (ap_compose' (λz : B × B, z.2)) at H2,
        rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
        krewrite prod.ap_pr2 at H2, krewrite prod_eq_pr2 at H2,
        apply H2 } },
    { intro qa, induction qa with a a a' r,
      { apply ap (class_of R), apply left_inv },
      { apply eq_pathover, rewrite [ap_id,(ap_compose' (quotient.elim _ _))],
        do 2 krewrite elim_eq_of_rel,
        have H1 : pathover (λz : A × A, R z.1 z.2)
          ((left_inv f a)⁻¹ ▸ (left_inv f a')⁻¹ ▸ r)
          (prod_eq (left_inv f a) (left_inv f a')) r,
        begin apply pathover_of_eq_tr, krewrite [prod_eq_inv,prod_eq_transport] end,
        have H2 : square
          (ap (λx : (Σz : A × A, R z.1 z.2), class_of R x.1.1)
            (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1))
          (ap (λx : (Σz : A × A, R z.1 z.2), class_of R x.1.2)
            (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1))
          (eq_of_rel R ((left_inv f a)⁻¹ ▸ (left_inv f a')⁻¹ ▸ r))
          (eq_of_rel R r),
        begin
          exact
          natural_square_tr (λw : (Σz : A × A, R z.1 z.2), eq_of_rel R w.2)
          (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1)
        end,
        krewrite (ap_compose' (class_of R)) at H2,
        krewrite (ap_compose' (λz : A × A, z.1)) at H2,
        rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
        krewrite prod.ap_pr1 at H2, krewrite prod_eq_pr1 at H2,
        krewrite (ap_compose' (class_of R) (λx : (Σz : A × A, R z.1 z.2), x.1.2)) at H2,
        krewrite (ap_compose' (λz : A × A, z.2)) at H2,
        rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
        krewrite prod.ap_pr2 at H2, krewrite prod_eq_pr2 at H2,
        have H3 :
          (k (f⁻¹ (f a)) (f⁻¹ (f a')))⁻¹
          ((right_inv f (f a))⁻¹ ▸ (right_inv f (f a'))⁻¹ ▸ k a a' r)
          = (left_inv f a)⁻¹ ▸ (left_inv f a')⁻¹ ▸ r,
        begin
          rewrite [adj f a,adj f a',ap_inv',ap_inv'],
          rewrite [-(tr_compose _ f (left_inv f a')⁻¹ (k a a' r)),
                   -(tr_compose _ f (left_inv f a)⁻¹)],
          rewrite [-(fn_tr_eq_tr_fn (left_inv f a')⁻¹ (λx, k a x) r),
                   -(fn_tr_eq_tr_fn (left_inv f a)⁻¹
                     (λx, k x (f⁻¹ (f a')))),
                   left_inv (k _ _)]
        end,
        rewrite H3, apply H2 } }
  end
end

section
  variables {A : Type} (R : A → A → Type)
             {B : Type} (Q : B → B → Type)
             (f : A ≃ B) (k : Πa a' : A, R a a' ≃ Q (f a) (f a'))
  include f k

  /- This could also be proved using ua, but then it wouldn't compute -/
  protected definition equiv : quotient R ≃ quotient Q :=
  equiv.mk (quotient.functor R Q f k) _
end


end quotient
