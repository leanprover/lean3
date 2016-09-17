/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Attributes of functors (full, faithful, split essentially surjective, ...)

Adjoint functors, isomorphisms and equivalences have their own file
-/

import .basic function arity

open eq functor trunc prod is_equiv iso equiv function is_trunc sigma

namespace category
  variables {C D E : Precategory} {F : C ⇒ D} {G : D ⇒ C}

  definition faithful [class] (F : C ⇒ D) := Π⦃c c' : C⦄ ⦃f f' : c ⟶ c'⦄, F f = F f' → f = f'
  definition full [class] (F : C ⇒ D) := Π⦃c c' : C⦄, is_surjective (@(to_fun_hom F) c c')
  definition fully_faithful [class] (F : C ⇒ D) := Π(c c' : C), is_equiv (@(to_fun_hom F) c c')
  definition split_essentially_surjective [class] (F : C ⇒ D) := Π(d : D), Σ(c : C), F c ≅ d
  definition essentially_surjective [class] (F : C ⇒ D) := Π(d : D), ∃(c : C), F c ≅ d

  definition is_weak_equivalence [class] (F : C ⇒ D) :=
  fully_faithful F × essentially_surjective F

  definition is_equiv_of_fully_faithful [instance] (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : is_equiv (@(to_fun_hom F) c c') :=
  !H

  definition fully_faithful_of_is_weak_equivalence [instance] (F : C ⇒ D)
    [H : is_weak_equivalence F] : fully_faithful F :=
  pr1 H

  definition essentially_surjective_of_is_weak_equivalence [instance] (F : C ⇒ D)
    [H : is_weak_equivalence F] : essentially_surjective F :=
  pr2 H

  definition hom_inv [reducible] (F : C ⇒ D) [H : fully_faithful F] {c c' : C} (f : F c ⟶ F c')
    : c ⟶ c' :=
  (to_fun_hom F)⁻¹ᶠ f

  definition hom_inv_respect_id (F : C ⇒ D) [H : fully_faithful F] (c : C) :
    hom_inv F (ID (F c)) = id :=
  begin
    apply eq_of_fn_eq_fn' (to_fun_hom F),
    exact !(right_inv (to_fun_hom F)) ⬝ !respect_id⁻¹,
  end

  definition hom_inv_respect_comp (F : C ⇒ D) [H : fully_faithful F] {a b c : C}
    (g : F b ⟶ F c) (f : F a ⟶ F b) : hom_inv F (g ∘ f) = hom_inv F g ∘ hom_inv F f :=
  begin
    apply eq_of_fn_eq_fn' (to_fun_hom F),
    refine !(right_inv (to_fun_hom F)) ⬝ _ ⬝ !respect_comp⁻¹,
    rewrite [right_inv (to_fun_hom F), right_inv (to_fun_hom F)],
  end

  definition reflect_is_iso [constructor] (F : C ⇒ D) [H : fully_faithful F] {c c' : C}
    (f : c ⟶ c') [H : is_iso (F f)] : is_iso f :=
  begin
    fconstructor,
    { exact (to_fun_hom F)⁻¹ᶠ (F f)⁻¹},
    { apply eq_of_fn_eq_fn' (to_fun_hom F),
      rewrite [respect_comp,right_inv (to_fun_hom F),respect_id,left_inverse]},
    { apply eq_of_fn_eq_fn' (to_fun_hom F),
      rewrite [respect_comp,right_inv (to_fun_hom F),respect_id,right_inverse]},
  end

  definition reflect_iso [constructor] (F : C ⇒ D) [H : fully_faithful F] {c c' : C}
    (f : F c ≅ F c') : c ≅ c' :=
  begin
    fconstructor,
    { exact (to_fun_hom F)⁻¹ᶠ f},
    { have H : is_iso (F ((to_fun_hom F)⁻¹ᶠ f)), from
        have H' : is_iso (to_hom f), from _,
        (right_inv (to_fun_hom F) (to_hom f))⁻¹ ▸ H',
      exact reflect_is_iso F _},
  end

  theorem reflect_inverse (F : C ⇒ D) [H : fully_faithful F] {c c' : C} (f : c ⟶ c')
    [H' : is_iso f] : (to_fun_hom F)⁻¹ᶠ (F f)⁻¹ = f⁻¹ :=
  @inverse_eq_inverse _ _ _ _ _ _ (reflect_is_iso F f) H' idp

  definition hom_equiv_F_hom_F [constructor] (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : (c ⟶ c') ≃ (F c ⟶ F c') :=
  equiv.mk _ !H

  definition iso_equiv_F_iso_F [constructor] (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : (c ≅ c') ≃ (F c ≅ F c') :=
  begin
    fapply equiv.MK,
    { exact to_fun_iso F},
    { apply reflect_iso F},
    { exact abstract begin
      intro f, induction f with f F', induction F' with g p q, apply iso_eq,
      esimp [reflect_iso], apply right_inv end end},
    { exact abstract begin
      intro f, induction f with f F', induction F' with g p q, apply iso_eq,
      esimp [reflect_iso], apply right_inv end end},
  end

  definition full_of_fully_faithful [instance] (F : C ⇒ D) [H : fully_faithful F] : full F :=
  λc c' g, tr (fiber.mk ((@(to_fun_hom F) c c')⁻¹ᶠ g) !right_inv)

  definition faithful_of_fully_faithful [instance] (F : C ⇒ D) [H : fully_faithful F]
    : faithful F :=
  λc c' f f' p, is_injective_of_is_embedding p

  definition is_embedding_of_faithful [instance] (F : C ⇒ D) [H : faithful F] (c c' : C)
    : is_embedding (to_fun_hom F : c ⟶ c' → F c ⟶ F c') :=
  begin
    apply is_embedding_of_is_injective,
    apply H
  end

  definition is_surjective_of_full [instance] (F : C ⇒ D) [H : full F] (c c' : C)
    : is_surjective (to_fun_hom F : c ⟶ c' → F c ⟶ F c') :=
  @H c c'

  definition fully_faithful_of_full_of_faithful (H : faithful F) (K : full F)
    : fully_faithful F :=
  begin
    intro c c',
    apply is_equiv_of_is_surjective_of_is_embedding,
  end

  theorem is_prop_fully_faithful [instance] (F : C ⇒ D) : is_prop (fully_faithful F) :=
  by unfold fully_faithful; exact _

  theorem is_prop_full [instance] (F : C ⇒ D) : is_prop (full F) :=
  by unfold full; exact _

  theorem is_prop_faithful [instance] (F : C ⇒ D) : is_prop (faithful F) :=
  by unfold faithful; exact _

  theorem is_prop_essentially_surjective [instance] (F : C ⇒ D)
    : is_prop (essentially_surjective F) :=
  by unfold essentially_surjective; exact _

  definition essentially_surjective_of_split_essentially_surjective [instance] (F : C ⇒ D)
    [H : split_essentially_surjective F] : essentially_surjective F :=
  λd, tr (H d)

  definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F ≃ (faithful F × full F) :=
  equiv_of_is_prop (λH, (faithful_of_fully_faithful F, full_of_fully_faithful F))
                    (λH, fully_faithful_of_full_of_faithful (pr1 H) (pr2 H))

/- alternative proof using direct calculation with equivalences

  definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F ≃ (faithful F × full F) :=
  calc
        fully_faithful F
      ≃ (Π(c c' : C), is_embedding (to_fun_hom F) × is_surjective (to_fun_hom F))
        : pi_equiv_pi_right (λc, pi_equiv_pi_right
            (λc', !is_equiv_equiv_is_embedding_times_is_surjective))
  ... ≃ (Π(c : C), (Π(c' : C), is_embedding  (to_fun_hom F)) ×
                   (Π(c' : C), is_surjective (to_fun_hom F)))
        : pi_equiv_pi_right (λc, !equiv_prod_corec)
  ... ≃ (Π(c c' : C), is_embedding (to_fun_hom F)) × full F
        : equiv_prod_corec
  ... ≃ faithful F × full F
        : prod_equiv_prod_right (pi_equiv_pi_right (λc, pi_equiv_pi_right
            (λc', !is_embedding_equiv_is_injective)))
-/

  definition fully_faithful_compose (G : D ⇒ E) (F : C ⇒ D) [fully_faithful G] [fully_faithful F] :
    fully_faithful (G ∘f F) :=
  λc c', is_equiv_compose (to_fun_hom G) (to_fun_hom F)

  definition full_compose (G : D ⇒ E) (F : C ⇒ D) [full G] [full F] : full (G ∘f F) :=
  λc c', is_surjective_compose (to_fun_hom G) (to_fun_hom F) _ _

  definition faithful_compose (G : D ⇒ E) (F : C ⇒ D) [H₁ : faithful G] [H₂ : faithful F] :
    faithful (G ∘f F) :=
  λc c' f f' p, H₂ (H₁ p)

  definition essentially_surjective_compose (G : D ⇒ E) (F : C ⇒ D) [H₁ : essentially_surjective G]
    [H₂ : essentially_surjective F] : essentially_surjective (G ∘f F) :=
  begin
    intro e,
    induction H₁ e with v, induction v with d p,
    induction H₂ d with w, induction w with c q,
    exact exists.intro c (to_fun_iso G q ⬝i p)
  end

  definition split_essentially_surjective_compose (G : D ⇒ E) (F : C ⇒ D)
    [H₁ : split_essentially_surjective G] [H₂ : split_essentially_surjective F]
    : split_essentially_surjective (G ∘f F) :=
  begin
    intro e, induction H₁ e with d p, induction H₂ d with c q,
    exact ⟨c, to_fun_iso G q ⬝i p⟩
  end

  /- we get the fact that the identity functor satisfies all these properties via the fact that it
     is an isomorphism -/


end category
