/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.equiv
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about the types equiv and is_equiv
-/

import types.fiber types.arrow arity

open eq is_trunc sigma sigma.ops arrow pi

namespace is_equiv
  open equiv function
  section
    open fiber
    variables {A B : Type} (f : A → B) [H : is_equiv f]
    include H
    definition is_contr_fiber_of_is_equiv (b : B) : is_contr (fiber f b) :=
    is_contr.mk
      (fiber.mk (f⁻¹ b) (right_inv f b))
      (λz, fiber.rec_on z (λa p, fiber_eq ((ap f⁻¹ p)⁻¹ ⬝ left_inv f a) (calc
        right_inv f b = (ap (f ∘ f⁻¹) p)⁻¹ ⬝ ((ap (f ∘ f⁻¹) p) ⬝ right_inv f b) : by rewrite inv_con_cancel_left
             ... = (ap (f ∘ f⁻¹) p)⁻¹ ⬝ (right_inv f (f a) ⬝ p)       : by rewrite ap_con_eq_con
             ... = (ap (f ∘ f⁻¹) p)⁻¹ ⬝ (ap f (left_inv f a) ⬝ p)    : by rewrite adj
             ... = (ap (f ∘ f⁻¹) p)⁻¹ ⬝ ap f (left_inv f a) ⬝ p      : by rewrite con.assoc
             ... = (ap f (ap f⁻¹ p))⁻¹ ⬝ ap f (left_inv f a) ⬝ p     : by rewrite ap_compose
             ... = ap f (ap f⁻¹ p)⁻¹ ⬝ ap f (left_inv f a) ⬝ p       : by rewrite ap_inv
             ... = ap f ((ap f⁻¹ p)⁻¹ ⬝ left_inv f a) ⬝ p            : by rewrite ap_con)))

    definition is_contr_right_inverse : is_contr (Σ(g : B → A), f ∘ g ∼ id) :=
    begin
      fapply is_trunc_equiv_closed,
        {apply sigma_equiv_sigma_id, intro g, apply eq_equiv_homotopy},
      fapply is_trunc_equiv_closed,
        {apply fiber.sigma_char},
      fapply is_contr_fiber_of_is_equiv,
      apply (to_is_equiv (arrow_equiv_arrow_right (equiv.mk f H))),
    end

    definition is_contr_right_coherence (u : Σ(g : B → A), f ∘ g ∼ id)
      : is_contr (Σ(η : u.1 ∘ f ∼ id), Π(a : A), u.2 (f a) = ap f (η a)) :=
    begin
      fapply is_trunc_equiv_closed,
        {apply equiv.symm, apply sigma_pi_equiv_pi_sigma},
      fapply is_trunc_equiv_closed,
        {apply pi_equiv_pi_id, intro a,
          apply (fiber_eq_equiv (fiber.mk (u.1 (f a)) (u.2 (f a))) (fiber.mk a idp))},
      fapply is_trunc_pi,
      intro a, fapply @is_contr_eq,
      apply is_contr_fiber_of_is_equiv
    end

  end
  variables {A B : Type} (f : A → B)

  protected definition sigma_char : (is_equiv f) ≃
  (Σ(g : B → A) (ε : f ∘ g ∼ id) (η : g ∘ f ∼ id), Π(a : A), ε (f a) = ap f (η a)) :=
  equiv.MK (λH, ⟨inv f, right_inv f, left_inv f, adj f⟩)
           (λp, is_equiv.mk f p.1 p.2.1 p.2.2.1 p.2.2.2)
           (λp, begin
                  cases p with [p1, p2],
                  cases p2 with [p21, p22],
                  cases p22 with [p221, p222],
                  apply idp
                end)
           (λH, is_equiv.rec_on H (λH1 H2 H3 H4, idp))

  protected definition sigma_char' : (is_equiv f) ≃
  (Σ(u : Σ(g : B → A), f ∘ g ∼ id), Σ(η : u.1 ∘ f ∼ id), Π(a : A), u.2 (f a) = ap f (η a)) :=
  calc
    (is_equiv f) ≃
      (Σ(g : B → A) (ε : f ∘ g ∼ id) (η : g ∘ f ∼ id), Π(a : A), ε (f a) = ap f (η a))
          : is_equiv.sigma_char
    ... ≃ (Σ(u : Σ(g : B → A), f ∘ g ∼ id), Σ(η : u.1 ∘ f ∼ id), Π(a : A), u.2 (f a) = ap f (η a))
          : {sigma_assoc_equiv (λu, Σ(η : u.1 ∘ f ∼ id), Π(a : A), u.2 (f a) = ap f (η a))}

  local attribute is_contr_right_inverse [instance] [priority 1600]
  local attribute is_contr_right_coherence [instance] [priority 1600]
  theorem is_hprop_is_equiv [instance] : is_hprop (is_equiv f) :=
  is_hprop_of_imp_is_contr (λ(H : is_equiv f), is_trunc_equiv_closed -2 (equiv.symm !sigma_char'))

  /- contractible fibers -/ -- TODO: uncomment this (needs to import instance is_hprop_is_trunc)
  -- definition is_contr_fun [reducible] {A B : Type} (f : A → B) := Π(b : B), is_contr (fiber f b)

  -- definition is_hprop_is_contr_fun (f : A → B) : is_hprop (is_contr_fun f) := _

  -- definition is_equiv_of_is_contr_fun [instance] [H : is_contr_fun f] : is_equiv f :=
  -- adjointify _ (λb, point (center (fiber f b)))
  --              (λb, point_eq (center (fiber f b)))
  --              (λa, ap point (contr (fiber.mk a idp)))

  -- definition is_equiv_of_imp_is_equiv (H : B → is_equiv f) : is_equiv f :=
  -- @is_equiv_of_is_contr_fun _ _ f (is_contr_fun.mk (λb, @is_contr_fiber_of_is_equiv _ _ _ (H b) _))

end is_equiv

namespace equiv
  open is_equiv
  variables {A B : Type}

  definition equiv_mk_eq {f f' : A → B} [H : is_equiv f] [H' : is_equiv f'] (p : f = f')
      : equiv.mk f H = equiv.mk f' H' :=
  apd011 equiv.mk p !is_hprop.elim

  definition equiv_eq {f f' : A ≃ B} (p : to_fun f = to_fun f') : f = f' :=
  by (cases f; cases f'; apply (equiv_mk_eq p))
end equiv
