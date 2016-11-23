/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Theorems about the unit type
-/

open is_equiv equiv option eq pointed is_trunc function

namespace unit

  protected definition eta : Π(u : unit), ⋆ = u
  | eta ⋆ := idp

  definition unit_equiv_option_empty [constructor] : unit ≃ option empty :=
  begin
    fapply equiv.MK,
    { intro u, exact none},
    { intro e, exact star},
    { intro e, cases e, reflexivity, contradiction},
    { intro u, cases u, reflexivity},
  end

  -- equivalences involving unit and other type constructors are in the file
  -- of the other constructor

  /- pointed and truncated unit -/

  definition punit [constructor] : Set* :=
  pSet.mk' unit

  notation `unit*` := punit

  definition unit_arrow_eq {X : Type} (f : unit → X) : (λx, f ⋆) = f :=
  by apply eq_of_homotopy; intro u; induction u; reflexivity

  open funext
  definition unit_arrow_eq_compose {X Y : Type} (g : X → Y) (f : unit → X) :
    unit_arrow_eq (g ∘ f) = ap (λf, g ∘ f) (unit_arrow_eq f) :=
  begin
    apply eq_of_fn_eq_fn' apd10,
    refine right_inv apd10 _ ⬝ _,
    refine _ ⬝ ap apd10 (!compose_eq_of_homotopy)⁻¹,
    refine _ ⬝ (right_inv apd10 _)⁻¹,
    apply eq_of_homotopy, intro u, induction u, reflexivity
  end

end unit
