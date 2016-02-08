/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the pushout
-/

import .quotient types.sigma types.arrow_2

open quotient eq sum equiv is_trunc

namespace pushout
section

parameters {TL BL TR : Type} (f : TL → BL) (g : TL → TR)

  local abbreviation A := BL + TR
  inductive pushout_rel : A → A → Type :=
  | Rmk : Π(x : TL), pushout_rel (inl (f x)) (inr (g x))
  open pushout_rel
  local abbreviation R := pushout_rel

  definition pushout : Type := quotient R -- TODO: define this in root namespace

  parameters {f g}
  definition inl (x : BL) : pushout :=
  class_of R (inl x)

  definition inr (x : TR) : pushout :=
  class_of R (inr x)

  definition glue (x : TL) : inl (f x) = inr (g x) :=
  eq_of_rel pushout_rel (Rmk f g x)

  protected definition rec {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
      (y : pushout) : P y :=
  begin
    induction y,
    { cases a,
        apply Pinl,
        apply Pinr},
    { cases H, apply Pglue}
  end

  protected definition rec_on [reducible] {P : pushout → Type} (y : pushout)
    (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x))
    (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x)) : P y :=
  rec Pinl Pinr Pglue y

  theorem rec_glue {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
      (x : TL) : apdo (rec Pinl Pinr Pglue) (glue x) = Pglue x :=
  !rec_eq_of_rel

  protected definition elim {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (y : pushout) : P :=
  rec Pinl Pinr (λx, pathover_of_eq (Pglue x)) y

  protected definition elim_on [reducible] {P : Type} (y : pushout) (Pinl : BL → P)
    (Pinr : TR → P) (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) : P :=
  elim Pinl Pinr Pglue y

  theorem elim_glue {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (x : TL)
    : ap (elim Pinl Pinr Pglue) (glue x) = Pglue x :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (glue x)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑pushout.elim,rec_glue],
  end

  protected definition elim_type (Pinl : BL → Type) (Pinr : TR → Type)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (y : pushout) : Type :=
  elim Pinl Pinr (λx, ua (Pglue x)) y

  protected definition elim_type_on [reducible] (y : pushout) (Pinl : BL → Type)
    (Pinr : TR → Type) (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) : Type :=
  elim_type Pinl Pinr Pglue y

  theorem elim_type_glue (Pinl : BL → Type) (Pinr : TR → Type)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (x : TL)
    : transport (elim_type Pinl Pinr Pglue) (glue x) = Pglue x :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue];apply cast_ua_fn

  protected definition rec_prop {P : pushout → Type} [H : Πx, is_prop (P x)]
    (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x)) (y : pushout) :=
  rec Pinl Pinr (λx, !is_prop.elimo) y

  protected definition elim_prop {P : Type} [H : is_prop P] (Pinl : BL → P) (Pinr : TR → P)
    (y : pushout) : P :=
  elim Pinl Pinr (λa, !is_prop.elim) y

end
end pushout

attribute pushout.inl pushout.inr [constructor]
attribute pushout.rec pushout.elim [unfold 10] [recursor 10]
attribute pushout.elim_type [unfold 9]
attribute pushout.rec_on pushout.elim_on [unfold 7]
attribute pushout.elim_type_on [unfold 6]

open sigma

namespace pushout

  variables {TL BL TR : Type} (f : TL → BL) (g : TL → TR)

  /- The non-dependent universal property -/
  definition pushout_arrow_equiv (C : Type)
    : (pushout f g → C) ≃ (Σ(i : BL → C) (j : TR → C), Πc, i (f c) = j (g c)) :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨λx, f (inl x), λx, f (inr x), λx, ap f (glue x)⟩},
    { intro v x, induction v with i w, induction w with j p, induction x,
        exact (i a), exact (j a), exact (p x)},
    { intro v, induction v with i w, induction w with j p, esimp,
      apply ap (λp, ⟨i, j, p⟩), apply eq_of_homotopy, intro x, apply elim_glue},
    { intro f, apply eq_of_homotopy, intro x, induction x: esimp,
      apply eq_pathover, apply hdeg_square, esimp, apply elim_glue},
  end

  /- glue squares -/
  protected definition glue_square {x x' : TL} (p : x = x')
    : square (glue x) (glue x') (ap inl (ap f p)) (ap inr (ap g p)) :=
  by cases p; apply vrefl

end pushout

open function sigma.ops

namespace pushout

  /- The flattening lemma -/
  section

    universe variable u
    parameters {TL BL TR : Type} (f : TL → BL) (g : TL → TR)
               (Pinl : BL → Type.{u}) (Pinr : TR → Type.{u})
               (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x))
    include Pglue

    local abbreviation A := BL + TR
    local abbreviation R : A → A → Type := pushout_rel f g
    local abbreviation P [unfold 5] := pushout.elim_type Pinl Pinr Pglue

    local abbreviation F : sigma (Pinl ∘ f) → sigma Pinl :=
    λz, ⟨ f z.1 , z.2 ⟩

    local abbreviation G : sigma (Pinl ∘ f) → sigma Pinr :=
    λz, ⟨ g z.1 , Pglue z.1 z.2 ⟩

    local abbreviation Pglue' : Π ⦃a a' : A⦄,
      R a a' → sum.rec Pinl Pinr a ≃ sum.rec Pinl Pinr a' :=
    @pushout_rel.rec TL BL TR f g
     (λ ⦃a a' ⦄ (r : R a a'),
       (sum.rec Pinl Pinr a) ≃ (sum.rec Pinl Pinr a')) Pglue

    protected definition flattening : sigma P ≃ pushout F G :=
    begin
      have H : Πz, P z ≃ quotient.elim_type (sum.rec Pinl Pinr) Pglue' z,
      begin
        intro z, apply equiv_of_eq,
        have H1 : pushout.elim_type Pinl Pinr Pglue
                  = quotient.elim_type (sum.rec Pinl Pinr) Pglue',
        begin
        change
      quotient.rec (sum.rec Pinl Pinr)
        (λa a' r, pushout_rel.cases_on r (λx, pathover_of_eq (ua (Pglue x))))
    = quotient.rec (sum.rec Pinl Pinr)
        (λa a' r, pathover_of_eq (ua (pushout_rel.cases_on r Pglue))),
          have H2 : Π⦃a a'⦄ r : pushout_rel f g a a',
      pushout_rel.cases_on r (λx, pathover_of_eq (ua (Pglue x)))
    = pathover_of_eq (ua (pushout_rel.cases_on r Pglue))
      :> sum.rec Pinl Pinr a =[eq_of_rel (pushout_rel f g) r]
         sum.rec Pinl Pinr a',
          begin intros a a' r, cases r, reflexivity end,
          rewrite (eq_of_homotopy3 H2)
        end,
        apply ap10 H1
      end,
      apply equiv.trans (sigma_equiv_sigma_right H),
      apply equiv.trans (quotient.flattening.flattening_lemma R (sum.rec Pinl Pinr) Pglue'),
      fapply equiv.MK,
      { intro q, induction q with z z z' fr,
        { induction z with a p, induction a with x x,
          { exact inl ⟨x, p⟩ },
          { exact inr ⟨x, p⟩ } },
        { induction fr with a a' r p, induction r with x,
          exact glue ⟨x, p⟩ } },
      { intro q, induction q with xp xp xp,
        { exact class_of _ ⟨sum.inl xp.1, xp.2⟩ },
        { exact class_of _ ⟨sum.inr xp.1, xp.2⟩ },
        { apply eq_of_rel, constructor } },
      { intro q, induction q with xp xp xp: induction xp with x p,
        { apply ap inl, reflexivity },
        { apply ap inr, reflexivity },
        { unfold F, unfold G, apply eq_pathover,
          rewrite [ap_id,ap_compose' (quotient.elim _ _)],
          krewrite elim_glue, krewrite elim_eq_of_rel, apply hrefl } },
      { intro q, induction q with z z z' fr,
        { induction z with a p, induction a with x x,
          { reflexivity },
          { reflexivity } },
        { induction fr with a a' r p, induction r with x,
          esimp, apply eq_pathover,
          rewrite [ap_id,ap_compose' (pushout.elim _ _ _)],
          krewrite elim_eq_of_rel, krewrite elim_glue, apply hrefl } }
    end
  end

  -- Commutativity of pushouts
  section
  variables {TL BL TR : Type} (f : TL → BL) (g : TL → TR)

  protected definition transpose [constructor] : pushout f g → pushout g f :=
  begin
    intro x, induction x, apply inr a, apply inl a, apply !glue⁻¹
  end

  --TODO prove without krewrite?
  protected definition transpose_involutive (x : pushout f g) :
    pushout.transpose g f (pushout.transpose f g x) = x :=
  begin
      induction x, apply idp, apply idp,
      apply eq_pathover, refine _ ⬝hp !ap_id⁻¹,
      refine !(ap_compose (pushout.transpose _ _)) ⬝ph _, esimp[pushout.transpose],
      krewrite [elim_glue, ap_inv, elim_glue, inv_inv], apply hrfl
  end

  protected definition symm : pushout f g ≃ pushout g f :=
  begin
    fapply equiv.MK, do 2 exact !pushout.transpose,
    do 2 (intro x; apply pushout.transpose_involutive),
  end

  end

  -- Functoriality of pushouts
  section
    section lemmas
      variables {X : Type} {x₀ x₁ x₂ x₃ : X}
                (p : x₀ = x₁) (q : x₁ = x₂) (r : x₂ = x₃)
      private definition is_equiv_functor_lemma₁
        : (r ⬝ ((p ⬝ q ⬝ r)⁻¹ ⬝ p)) = q⁻¹ :=
      by cases p; cases r; cases q; reflexivity

      private definition is_equiv_functor_lemma₂
        : (p ⬝ q ⬝ r)⁻¹ ⬝ (p ⬝ q) = r⁻¹ :=
      by cases p; cases r; cases q; reflexivity
    end lemmas

    variables {TL BL TR : Type} (f : TL → BL) (g : TL → TR)
              {TL' BL' TR' : Type} (f' : TL' → BL') (g' : TL' → TR')
              (tl : TL → TL') (bl : BL → BL') (tr : TR → TR')
              (fh : bl ∘ f ~ f' ∘ tl) (gh : tr ∘ g ~ g' ∘ tl)
    include fh gh

    protected definition functor [reducible] : pushout f g → pushout f' g' :=
    begin
      intro x, induction x with a b z,
      { exact inl (bl a) },
      { exact inr (tr b) },
      { exact (ap inl (fh z)) ⬝ glue (tl z) ⬝ (ap inr (gh z)⁻¹) }
    end

    protected definition ap_functor_inl [reducible] {x x' : BL} (p : x = x')
      : ap (pushout.functor f g f' g' tl bl tr fh gh) (ap inl p) = ap inl (ap bl p) :=
    by cases p; reflexivity

    protected definition ap_functor_inr [reducible] {x x' : TR} (p : x = x')
      : ap (pushout.functor f g f' g' tl bl tr fh gh) (ap inr p) = ap inr (ap tr p) :=
    by cases p; reflexivity

    variables [ietl : is_equiv tl] [iebl : is_equiv bl] [ietr : is_equiv tr]
    include ietl iebl ietr

    open equiv is_equiv arrow
    protected definition is_equiv_functor [instance]
      : is_equiv (pushout.functor f g f' g' tl bl tr fh gh) :=
    adjointify
      (pushout.functor f g f' g' tl bl tr fh gh)
      (pushout.functor f' g' f g tl⁻¹ bl⁻¹ tr⁻¹
        (inv_commute_of_commute tl bl f f' fh)
        (inv_commute_of_commute tl tr g g' gh))
    abstract begin
      intro x', induction x' with a' b' z',
      { apply ap inl, apply right_inv },
      { apply ap inr, apply right_inv },
      { apply eq_pathover,
        rewrite [ap_id,ap_compose' (pushout.functor f g f' g' tl bl tr fh gh)],
        krewrite elim_glue,
        rewrite [ap_inv,ap_con,ap_inv],
        krewrite [pushout.ap_functor_inr], rewrite ap_con,
        krewrite [pushout.ap_functor_inl,elim_glue],
        apply transpose,
        apply move_top_of_right, apply move_top_of_left',
        krewrite [-(ap_inv inl),-ap_con,-(ap_inv inr),-ap_con],
        apply move_top_of_right, apply move_top_of_left',
        krewrite [-ap_con,-(ap_inv inl),-ap_con],
        rewrite ap_bot_inv_commute_of_commute,
        apply eq_hconcat (ap02 inl
          (is_equiv_functor_lemma₁
            (right_inv bl (f' z'))
            (ap f' (right_inv tl z')⁻¹)
            (fh (tl⁻¹ z'))⁻¹)),
        rewrite [ap_inv f',inv_inv],
        rewrite ap_bot_inv_commute_of_commute,
        refine hconcat_eq _ (ap02 inr
          (is_equiv_functor_lemma₁
            (right_inv tr (g' z'))
            (ap g' (right_inv tl z')⁻¹)
            (gh (tl⁻¹ z'))⁻¹))⁻¹,
        rewrite [ap_inv g',inv_inv],
        apply pushout.glue_square }
    end end
    abstract begin
      intro x, induction x with a b z,
      { apply ap inl, apply left_inv },
      { apply ap inr, apply left_inv },
      { apply eq_pathover,
        rewrite [ap_id,ap_compose'
          (pushout.functor f' g' f g tl⁻¹ bl⁻¹ tr⁻¹ _ _)
          (pushout.functor f g f' g' tl bl tr _ _)],
        krewrite elim_glue,
        rewrite [ap_inv,ap_con,ap_inv],
        krewrite [pushout.ap_functor_inr], rewrite ap_con,
        krewrite [pushout.ap_functor_inl,elim_glue],
        apply transpose,
        apply move_top_of_right, apply move_top_of_left',
        krewrite [-(ap_inv inl),-ap_con,-(ap_inv inr),-ap_con],
        apply move_top_of_right, apply move_top_of_left',
        krewrite [-ap_con,-(ap_inv inl),-ap_con],
        rewrite inv_commute_of_commute_top,
        apply eq_hconcat (ap02 inl
          (is_equiv_functor_lemma₂
            (ap bl⁻¹ (fh z))⁻¹
            (left_inv bl (f z))
            (ap f (left_inv tl z)⁻¹))),
        rewrite [ap_inv f,inv_inv],
        rewrite inv_commute_of_commute_top,
        refine hconcat_eq _ (ap02 inr
          (is_equiv_functor_lemma₂
            (ap tr⁻¹ (gh z))⁻¹
            (left_inv tr (g z))
            (ap g (left_inv tl z)⁻¹)))⁻¹,
        rewrite [ap_inv g,inv_inv],
        apply pushout.glue_square }
    end end

  end
end pushout
