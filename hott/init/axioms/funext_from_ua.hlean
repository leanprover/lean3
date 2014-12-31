-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
prelude
import ..equiv ..datatypes ..types.prod
import .funext_varieties .ua .funext

open eq function prod sigma truncation equiv is_equiv unit

context
  universe variables l

  protected theorem ua_isequiv_postcompose {A B : Type.{l}} {C : Type}
      {w : A → B} {H0 : is_equiv w} : is_equiv (@compose C A B w) :=
    let w' := equiv.mk w H0 in
    let eqinv : A = B := ((@is_equiv.inv _ _ _ (ua_is_equiv A B)) w') in
    let eq' := equiv_path eqinv in
    is_equiv.adjointify (@compose C A B w)
      (@compose C B A (is_equiv.inv w))
      (λ (x : C → B),
        have eqretr : eq' = w',
          from (@retr _ _ (@equiv_path A B) (ua_is_equiv A B) w'),
        have invs_eq : (to_fun eq')⁻¹ = (to_fun w')⁻¹,
          from inv_eq eq' w' eqretr,
        have eqfin : (to_fun eq') ∘ ((to_fun eq')⁻¹ ∘ x) = x,
          from (λ p,
            (@eq.rec_on Type.{l} A
              (λ B' p', Π (x' : C → B'), (to_fun (equiv_path p'))
                ∘ ((to_fun (equiv_path p'))⁻¹ ∘ x') = x')
              B p (λ x', idp))
            ) eqinv x,
        have eqfin' : (to_fun w') ∘ ((to_fun eq')⁻¹ ∘ x) = x,
          from eqretr ▹ eqfin,
        have eqfin'' : (to_fun w') ∘ ((to_fun w')⁻¹ ∘ x) = x,
          from invs_eq ▹ eqfin',
        eqfin''
      )
      (λ (x : C → A),
        have eqretr : eq' = w',
          from (@retr _ _ (@equiv_path A B) (ua_is_equiv A B) w'),
        have invs_eq : (to_fun eq')⁻¹ = (to_fun w')⁻¹,
          from inv_eq eq' w' eqretr,
        have eqfin : (to_fun eq')⁻¹ ∘ ((to_fun eq') ∘ x) = x,
          from (λ p, eq.rec_on p idp) eqinv,
        have eqfin' : (to_fun eq')⁻¹ ∘ ((to_fun w') ∘ x) = x,
          from eqretr ▹ eqfin,
        have eqfin'' : (to_fun w')⁻¹ ∘ ((to_fun w') ∘ x) = x,
          from invs_eq ▹ eqfin',
        eqfin''
      )

  -- We are ready to prove functional extensionality,
  -- starting with the naive non-dependent version.
  protected definition diagonal [reducible] (B : Type) : Type
    := Σ xy : B × B, pr₁ xy = pr₂ xy

  protected definition isequiv_src_compose {A B : Type}
      : @is_equiv (A → diagonal B)
                 (A → B)
                 (compose (pr₁ ∘ pr1)) :=
    @ua_isequiv_postcompose _ _ _ (pr₁ ∘ pr1)
        (is_equiv.adjointify (pr₁ ∘ pr1)
          (λ x, sigma.mk (x , x) idp) (λx, idp)
          (λ x, sigma.rec_on x
            (λ xy, prod.rec_on xy
              (λ b c p, eq.rec_on p idp))))

  protected definition isequiv_tgt_compose {A B : Type}
      : @is_equiv (A → diagonal B)
                 (A → B)
                 (compose (pr₂ ∘ pr1)) :=
    @ua_isequiv_postcompose _ _ _ (pr2 ∘ pr1)
        (is_equiv.adjointify (pr2 ∘ pr1)
          (λ x, sigma.mk (x , x) idp) (λx, idp)
          (λ x, sigma.rec_on x
            (λ xy, prod.rec_on xy
              (λ b c p, eq.rec_on p idp))))

  theorem nondep_funext_from_ua {A : Type} {B : Type}
      : Π {f g : A → B}, f ∼ g → f = g :=
    (λ (f g : A → B) (p : f ∼ g),
        let d := λ (x : A), sigma.mk (f x , f x) idp in
        let e := λ (x : A), sigma.mk (f x , g x) (p x) in
        let precomp1 :=  compose (pr₁ ∘ pr1) in
        have equiv1 [visible] : is_equiv precomp1,
          from @isequiv_src_compose A B,
        have equiv2 [visible] : Π x y, is_equiv (ap precomp1),
          from is_equiv.ap_closed precomp1,
        have H' : Π (x y : A → diagonal B),
            pr₁ ∘ pr1 ∘ x = pr₁ ∘ pr1 ∘ y → x = y,
          from (λ x y, is_equiv.inv (ap precomp1)),
        have eq2 : pr₁ ∘ pr1 ∘ d = pr₁ ∘ pr1 ∘ e,
          from idp,
        have eq0 : d = e,
          from H' d e eq2,
        have eq1 : (pr₂ ∘ pr1) ∘ d = (pr₂ ∘ pr1) ∘ e,
          from ap _ eq0,
        eq1
    )

end

-- Now we use this to prove weak funext, which as we know
-- implies (with dependent eta) also the strong dependent funext.
theorem weak_funext_from_ua : weak_funext :=
  (λ (A : Type) (P : A → Type) allcontr,
    let U := (λ (x : A), unit) in
  have pequiv : Π (x : A), P x ≃ U x,
    from (λ x, @equiv_contr_unit(P x) (allcontr x)),
  have psim : Π (x : A), P x = U x,
    from (λ x, @is_equiv.inv _ _
      equiv_path (ua_is_equiv _ _) (pequiv x)),
  have p : P = U,
    from @nondep_funext_from_ua A Type P U psim,
  have tU' : is_contr (A → unit),
    from is_contr.mk (λ x, ⋆)
      (λ f, @nondep_funext_from_ua A unit (λ x, ⋆) f
        (λ x, unit.rec_on (f x) idp)),
  have tU : is_contr (Π x, U x),
    from tU',
  have tlast : is_contr (Πx, P x),
    from eq.transport _ (p⁻¹) tU,
  tlast
)

-- In the following we will proof function extensionality using the univalence axiom
definition funext_from_ua [instance] : funext :=
  funext_from_weak_funext (@weak_funext_from_ua)
