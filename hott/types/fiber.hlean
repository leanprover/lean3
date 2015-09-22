/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about fibers
-/

import .sigma .eq .pi .pointed

structure fiber {A B : Type} (f : A → B) (b : B) :=
  (point : A)
  (point_eq : f point = b)

open equiv sigma sigma.ops eq pi

namespace fiber
  variables {A B : Type} {f : A → B} {b : B}

  protected definition sigma_char [constructor]
    (f : A → B) (b : B) : fiber f b ≃ (Σ(a : A), f a = b) :=
  begin
  fapply equiv.MK,
    {intro x, exact ⟨point x, point_eq x⟩},
    {intro x, exact (fiber.mk x.1 x.2)},
    {intro x, cases x, apply idp},
    {intro x, cases x, apply idp},
  end

  definition fiber_eq_equiv (x y : fiber f b)
    : (x = y) ≃ (Σ(p : point x = point y), point_eq x = ap f p ⬝ point_eq y) :=
  begin
    apply equiv.trans,
      apply eq_equiv_fn_eq_of_equiv, apply fiber.sigma_char,
    apply equiv.trans,
      apply sigma_eq_equiv,
    apply sigma_equiv_sigma_id,
    intro p,
    apply pathover_eq_equiv_Fl,
  end

  definition fiber_eq {x y : fiber f b} (p : point x = point y)
    (q : point_eq x = ap f p ⬝ point_eq y) : x = y :=
  to_inv !fiber_eq_equiv ⟨p, q⟩

  open is_trunc
  definition fiber_pr1 (B : A → Type) (a : A) : fiber (pr1 : (Σa, B a) → A) a ≃ B a :=
  calc
    fiber pr1 a ≃ Σu, u.1 = a            : fiber.sigma_char
            ... ≃ Σa' (b : B a'), a' = a : sigma_assoc_equiv
            ... ≃ Σa' (p : a' = a), B a' : sigma_equiv_sigma_id (λa', !comm_equiv_nondep)
            ... ≃ Σu, B u.1              : sigma_assoc_equiv
            ... ≃ B a                    : !sigma_equiv_of_is_contr_left

  definition sigma_fiber_equiv (f : A → B) : (Σb, fiber f b) ≃ A :=
  calc
    (Σb, fiber f b) ≃ Σb a, f a = b : sigma_equiv_sigma_id (λb, !fiber.sigma_char)
                ... ≃ Σa b, f a = b : sigma_comm_equiv
                ... ≃ A             : sigma_equiv_of_is_contr_right

  definition is_pointed_fiber [instance] [constructor] (f : A → B) (a : A)
    : pointed (fiber f (f a)) :=
  pointed.mk (fiber.mk a idp)

  definition pointed_fiber [constructor] (f : A → B) (a : A) : Type* :=
  Pointed.mk (fiber.mk a (idpath (f a)))

end fiber
