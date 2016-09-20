/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

import .iso algebra.bundled

open eq is_trunc iso category algebra nat unit

namespace category

  structure groupoid [class] (ob : Type) extends parent : precategory ob :=
  mk' :: (all_iso : Π ⦃a b : ob⦄ (f : hom a b), @is_iso ob parent a b f)

  abbreviation all_iso := @groupoid.all_iso
  attribute groupoid.all_iso [instance] [priority 3000]
  attribute groupoid.to_precategory [unfold 2]
  definition groupoid.mk [reducible] [constructor] {ob : Type} (C : precategory ob)
    (H : Π (a b : ob) (f : a ⟶ b), is_iso f) : groupoid ob :=
  precategory.rec_on C groupoid.mk' H

  definition groupoid_of_group.{l} [constructor] (A : Type.{l}) [G : group A] :
    groupoid.{0 l} unit :=
  begin
    fapply groupoid.mk; fapply precategory.mk: intros,
      { exact A},
      { exact _},
      { exact a_2 * a_1},
      { exact 1},
      { apply mul.assoc},
      { apply mul_one},
      { apply one_mul},
      { esimp [precategory.mk],
        fapply is_iso.mk,
        { exact f⁻¹},
        { apply mul.right_inv},
        { apply mul.left_inv}},
  end

  definition hom_group [constructor] {A : Type} [G : groupoid A] (a : A) : group (hom a a) :=
  begin
    fapply group.mk,
      intro f g, apply (comp f g),
      apply is_set_hom,
      intros f g h, apply (assoc f g h)⁻¹,
      apply (ID a),
      intro f, apply id_left,
      intro f, apply id_right,
      intro f, exact (iso.inverse f),
      intro f, exact (iso.left_inverse f),
  end

  definition group_of_is_contr_groupoid {ob : Type} [H : is_contr ob]
    [G : groupoid ob] : group (hom (center ob) (center ob)) := !hom_group
  definition group_of_groupoid_unit [G : groupoid unit] : group (hom ⋆ ⋆) := !hom_group

  -- Bundled version of categories
  -- we don't use Groupoid.carrier explicitly, but rather use Groupoid.carrier (to_Precategory C)
  structure Groupoid : Type :=
    (carrier : Type)
    (struct : groupoid carrier)

  attribute Groupoid.struct [instance] [coercion]

  definition Groupoid.to_Precategory [coercion] [reducible] [unfold 1] (C : Groupoid)
    : Precategory :=
  Precategory.mk (Groupoid.carrier C) _

  attribute Groupoid._trans_of_to_Precategory_1 [unfold 1]

  definition groupoid.Mk [reducible] [constructor] := Groupoid.mk
  definition groupoid.MK [reducible] [constructor] (C : Precategory)
    (H : Π (a b : C) (f : a ⟶ b), is_iso f) : Groupoid :=
  Groupoid.mk C (groupoid.mk C H)

  definition Groupoid.eta [unfold 1] (C : Groupoid) : Groupoid.mk C C = C :=
  Groupoid.rec (λob c, idp) C

  definition Groupoid_of_Group [constructor] (G : Group) : Groupoid :=
  Groupoid.mk unit (groupoid_of_group G)

end category
