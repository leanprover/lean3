/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Turn a subgroup into a group on the corresponding subtype. Given

  variables {A : Type} [group A] (G : set A) [is_subgroup G]

we have:

  group_of G      := G, viewed as a group
  to_group_of G a := if a is in G, returns the image in group_of G, or 1 otherwise
  to_subgroup a   := given a : group_of G, return the underlying element
-/
import .basic
open set function subtype classical

variables {A B C : Type}

namespace group_theory

definition group_of (G : set A) : Type := subtype G

definition subgroup_to_group {G : set A} ⦃a : A⦄ (aG : a ∈ G) : group_of G := tag a aG

definition to_subgroup {G : set A} (a : group_of G) : A := elt_of a

proposition to_subgroup_mem {G : set A} (a : group_of G) : to_subgroup a ∈ G := has_property a

variables [group A] (G : set A) [is_subgroup G]

definition group_of.group [instance] : group (group_of G) :=
⦃ group,
  mul          := λ a b,  subgroup_to_group (mul_mem (to_subgroup_mem a) (to_subgroup_mem b)),
  mul_assoc    := λ a b c, subtype.eq !mul.assoc,
  one          := subgroup_to_group (@one_mem A _ G _),
  one_mul      := λ a, subtype.eq !one_mul,
  mul_one      := λ a, subtype.eq !mul_one,
  inv          := λ a, tag (elt_of a)⁻¹ (inv_mem (to_subgroup_mem a)),
  mul_left_inv := λ a, subtype.eq !mul.left_inv
⦄

proposition is_hom_group_to_subgroup [instance] : is_hom (@to_subgroup A G) :=
is_mul_hom.mk
  (take g₁ g₂ : group_of G,
    show to_subgroup (g₁ * g₂) = to_subgroup g₁ * to_subgroup g₂,
      by cases g₁; cases g₂; reflexivity)

noncomputable definition to_group_of (a : A) : group_of G :=
if H : a ∈ G then subgroup_to_group H else 1

proposition is_hom_on_to_group_of [instance] : is_hom_on (to_group_of G) G :=
take g₁, assume g₁G, take g₂, assume g₂G,
show to_group_of G (g₁ * g₂) = to_group_of G g₁ * to_group_of G g₂,
  by rewrite [↑to_group_of, dif_pos g₁G, dif_pos g₂G, dif_pos (mul_mem g₁G g₂G)]

proposition to_group_to_subgroup : left_inverse (to_group_of G) to_subgroup :=
begin
  intro a, rewrite [↑to_group_of, dif_pos (to_subgroup_mem a)],
  apply subtype.eq, reflexivity
end

-- proposition to_subgroup_to_group {a : A} (aG : a ∈ G) : to_subgroup (to_group_of G a) = a :=
-- by rewrite [↑to_group_of, dif_pos aG]
-- curiously, in the next version, "by rewrite [↑to_group_of, dif_pos aG]" doesn't work.

proposition to_subgroup_to_group : left_inv_on to_subgroup (to_group_of G) G :=
λ a aG, by xrewrite [dif_pos aG]

variable {G}
proposition inj_on_to_group_of : inj_on (to_group_of G) G :=
inj_on_of_left_inv_on (to_subgroup_to_group G)
variable (G)

proposition surj_on_to_group_of_univ : surj_on (to_group_of G) G univ :=
take y, assume yuniv, mem_image (to_subgroup_mem y) (to_group_to_subgroup G y)

proposition image_to_group_of_eq_univ : to_group_of G ' G = univ :=
image_eq_of_maps_to_of_surj_on (maps_to_univ _ _) (surj_on_to_group_of_univ G)

proposition surjective_to_group_of : surjective (to_group_of G) :=
surjective_of_has_right_inverse (exists.intro _ (to_group_to_subgroup G))

variable {G}
proposition to_group_of_preimage_to_group_of_image {S : set A} (SsubG : S ⊆ G) :
  (to_group_of G) '- (to_group_of G ' S) ∩ G = S :=
ext (take x, iff.intro
  (assume H,
    obtain Hx (xG : x ∈ G), from H,
    have to_group_of G x ∈ to_group_of G ' S, from mem_of_mem_preimage Hx,
    obtain y [(yS : y ∈ S) (Heq : to_group_of G y = to_group_of G x)], from this,
    have y = x, from inj_on_to_group_of (SsubG yS) xG Heq,
    show x ∈ S, by rewrite -this; exact yS)
  (assume xS, and.intro
     (mem_preimage (show to_group_of G x ∈ to_group_of G ' S, from mem_image_of_mem _ xS))
     (SsubG xS)))

end group_theory
