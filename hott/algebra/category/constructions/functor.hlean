/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Functor precategory and category
-/

import .opposite ..functor.attributes

open eq category is_trunc nat_trans iso is_equiv category.hom trunc

namespace functor

  definition precategory_functor [instance] [constructor] (D C : Precategory)
    : precategory (functor C D) :=
  precategory.mk (λa b, nat_trans a b)
                 (λ a b c g f, nat_trans.compose g f)
                 (λ a, nat_trans.id)
                 (λ a b c d h g f, !nat_trans.assoc)
                 (λ a b f, !nat_trans.id_left)
                 (λ a b f, !nat_trans.id_right)

  definition Precategory_functor [reducible] [constructor] (D C : Precategory) : Precategory :=
  precategory.Mk (precategory_functor D C)

  infixr ` ^c `:80 := Precategory_functor

  section
  /- we prove that if a natural transformation is pointwise an iso, then it is an iso -/
  variables {C D : Precategory} {F G : C ⇒ D} (η : F ⟹ G) [iso : Π(a : C), is_iso (η a)]
  include iso

  definition nat_trans_inverse [constructor] : G ⟹ F :=
  nat_trans.mk
    (λc, (η c)⁻¹)
    (λc d f,
    abstract begin
      apply comp_inverse_eq_of_eq_comp,
      transitivity (natural_map η d)⁻¹ ∘ to_fun_hom G f ∘ natural_map η c,
        {apply eq_inverse_comp_of_comp_eq, symmetry, apply naturality},
        {apply assoc}
    end end)

  definition nat_trans_left_inverse : nat_trans_inverse η ∘n η = 1 :=
  begin
    fapply (apdt011 nat_trans.mk),
      apply eq_of_homotopy, intro c, apply left_inverse,
    apply eq_of_homotopy3, intros, apply is_set.elim
  end

  definition nat_trans_right_inverse : η ∘n nat_trans_inverse η = 1 :=
  begin
    fapply (apdt011 nat_trans.mk),
      apply eq_of_homotopy, intro c, apply right_inverse,
    apply eq_of_homotopy3, intros, apply is_set.elim
  end

  definition is_natural_iso [constructor] : is_iso η :=
  is_iso.mk _ (nat_trans_left_inverse η) (nat_trans_right_inverse η)

  variable (iso)
  definition natural_iso.mk [constructor] : F ≅ G :=
  iso.mk _ (is_natural_iso η)

  omit iso

  variables (F G)
  definition is_natural_inverse (η : Πc, F c ≅ G c)
    (nat : Π⦃a b : C⦄ (f : hom a b), G f ∘ to_hom (η a) = to_hom (η b) ∘ F f)
    {a b : C} (f : hom a b) : F f ∘ to_inv (η a) = to_inv (η b) ∘ G f :=
  let η' : F ⟹ G := nat_trans.mk (λc, to_hom (η c)) @nat in
  naturality (nat_trans_inverse η') f

  definition is_natural_inverse' (η₁ : Πc, F c ≅ G c) (η₂ : F ⟹ G) (p : η₁ ~ η₂)
    {a b : C} (f : hom a b) : F f ∘ to_inv (η₁ a) = to_inv (η₁ b) ∘ G f :=
  is_natural_inverse F G η₁ abstract λa b g, (p a)⁻¹ ▸ (p b)⁻¹ ▸ naturality η₂ g end f

  variables {F G}
  definition natural_iso.MK [constructor]
    (η : Πc, F c ⟶ G c) (p : Π(c c' : C) (f : c ⟶ c'), G f ∘ η c = η c' ∘ F f)
    (θ : Πc, G c ⟶ F c) (r : Πc, θ c ∘ η c = id) (q : Πc, η c ∘ θ c = id) : F ≅ G :=
  iso.mk (nat_trans.mk η p) (@(is_natural_iso _) (λc, is_iso.mk (θ c) (r c) (q c)))

  definition natural_iso.mk' [constructor]
    (η : Πc, F c ≅ G c) (p : Π(c c' : C) (f : c ⟶ c'), G f ∘ to_hom (η c) = to_hom (η c') ∘ F f) :
    F ≅ G :=
  natural_iso.MK (λc, to_hom (η c)) p (λc, to_inv (η c))
                 (λc, to_left_inverse (η c)) (λc, to_right_inverse (η c))

  end

  section
  /- and conversely, if a natural transformation is an iso, it is componentwise an iso -/
  variables {A B C D : Precategory} {F G : C ⇒ D} (η : hom F G) [isoη : is_iso η] (c : C)
  include isoη
  definition componentwise_is_iso [constructor] : is_iso (η c) :=
  @is_iso.mk _ _ _ _ _ (natural_map η⁻¹ c) (ap010 natural_map ( left_inverse η) c)
                                           (ap010 natural_map (right_inverse η) c)

  local attribute componentwise_is_iso [instance]

  variable {isoη}
  definition natural_map_inverse : natural_map η⁻¹ c = (η c)⁻¹ := idp
  variable [isoη]

  definition naturality_iso {c c' : C} (f : c ⟶ c') : G f = η c' ∘ F f ∘ (η c)⁻¹ :=
  calc
    G f = (G f ∘ η c) ∘ (η c)⁻¹  : by rewrite comp_inverse_cancel_right
    ... = (η c' ∘ F f) ∘ (η c)⁻¹ : by rewrite naturality
    ... = η c' ∘ F f ∘ (η c)⁻¹   : by rewrite assoc

  definition naturality_iso' {c c' : C} (f : c ⟶ c') : (η c')⁻¹ ∘ G f ∘ η c = F f :=
  calc
   (η c')⁻¹ ∘ G f ∘ η c = (η c')⁻¹ ∘ η c' ∘ F f : by rewrite naturality
                    ... = F f                   : by rewrite inverse_comp_cancel_left

  omit isoη

  definition componentwise_iso [constructor] (η : F ≅ G) (c : C) : F c ≅ G c :=
  iso.mk (natural_map (to_hom η) c)
         (@componentwise_is_iso _ _ _ _ (to_hom η) (struct η) c)

  definition componentwise_iso_id (c : C) : componentwise_iso (iso.refl F) c = iso.refl (F c) :=
  iso_eq (idpath (ID (F c)))

  definition componentwise_iso_iso_of_eq (p : F = G) (c : C)
    : componentwise_iso (iso_of_eq p) c = iso_of_eq (ap010 to_fun_ob p c) :=
  eq.rec_on p !componentwise_iso_id

  theorem naturality_iso_id {F : C ⇒ C} (η : F ≅ 1) (c : C)
    : componentwise_iso η (F c) = F (componentwise_iso η c) :=
  comp.cancel_left (to_hom (componentwise_iso η c))
    ((naturality (to_hom η)) (to_hom (componentwise_iso η c)))

  definition natural_map_hom_of_eq (p : F = G) (c : C)
    : natural_map (hom_of_eq p) c = hom_of_eq (ap010 to_fun_ob p c) :=
  eq.rec_on p idp

  definition natural_map_inv_of_eq (p : F = G) (c : C)
    : natural_map (inv_of_eq p) c = hom_of_eq (ap010 to_fun_ob p c)⁻¹ :=
  eq.rec_on p idp

  definition hom_of_eq_compose_right {H : B ⇒ C} (p : F = G)
    : hom_of_eq (ap (λx, x ∘f H) p) = hom_of_eq p ∘nf H :=
  eq.rec_on p idp

  definition inv_of_eq_compose_right {H : B ⇒ C} (p : F = G)
    : inv_of_eq (ap (λx, x ∘f H) p) = inv_of_eq p ∘nf H :=
  eq.rec_on p idp

  definition hom_of_eq_compose_left {H : D ⇒ C} (p : F = G)
    : hom_of_eq (ap (λx, H ∘f x) p) = H ∘fn hom_of_eq p :=
  by induction p; exact !fn_id⁻¹

  definition inv_of_eq_compose_left {H : D ⇒ C} (p : F = G)
    : inv_of_eq (ap (λx, H ∘f x) p) = H ∘fn inv_of_eq p :=
  by induction p; exact !fn_id⁻¹

  definition assoc_natural [constructor] (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B)
    : H ∘f (G ∘f F) ⟹ (H ∘f G) ∘f F :=
  change_natural_map (hom_of_eq !functor.assoc)
                     (λa, id)
                     (λa, !natural_map_hom_of_eq ⬝ ap hom_of_eq !ap010_assoc)

  definition assoc_natural_rev [constructor] (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B)
    : (H ∘f G) ∘f F ⟹ H ∘f (G ∘f F) :=
  change_natural_map (inv_of_eq !functor.assoc)
                     (λa, id)
                     (λa, !natural_map_inv_of_eq ⬝ ap (λx, hom_of_eq x⁻¹) !ap010_assoc)

  definition assoc_iso [constructor] (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B)
    : H ∘f (G ∘f F) ≅ (H ∘f G) ∘f F :=
  iso.MK (assoc_natural H G F) (assoc_natural_rev H G F)
         (nat_trans_eq (λa, proof !id_id qed)) (nat_trans_eq (λa, proof !id_id qed))

  definition id_left_natural [constructor] (F : C ⇒ D) : functor.id ∘f F ⟹ F :=
  change_natural_map
    (hom_of_eq !functor.id_left)
    (λc, id)
    (λc, by induction F; exact !natural_map_hom_of_eq ⬝ ap hom_of_eq !ap010_functor_mk_eq_constant)


  definition id_left_natural_rev [constructor] (F : C ⇒ D) : F ⟹ functor.id ∘f F :=
  change_natural_map
    (inv_of_eq !functor.id_left)
    (λc, id)
    (λc, by induction F; exact !natural_map_inv_of_eq ⬝
                                 ap (λx, hom_of_eq x⁻¹) !ap010_functor_mk_eq_constant)

  definition id_right_natural [constructor] (F : C ⇒ D) : F ∘f functor.id ⟹ F :=
  change_natural_map
    (hom_of_eq !functor.id_right)
    (λc, id)
    (λc, by induction F; exact !natural_map_hom_of_eq ⬝ ap hom_of_eq !ap010_functor_mk_eq_constant)

  definition id_right_natural_rev [constructor] (F : C ⇒ D) : F ⟹ F ∘f functor.id :=
  change_natural_map
    (inv_of_eq !functor.id_right)
    (λc, id)
    (λc, by induction F; exact !natural_map_inv_of_eq ⬝
                                 ap (λx, hom_of_eq x⁻¹) !ap010_functor_mk_eq_constant)

  end

  section
  variables {C D E : Precategory} {G G' : D ⇒ E} {F F' : C ⇒ D} {J : D ⇒ D}

  definition is_iso_nf_compose [constructor] (G : D ⇒ E) (η : F ⟹ F') [H : is_iso η]
    : is_iso (G ∘fn η) :=
  is_iso.mk
    (G ∘fn @inverse (C ⇒ D) _ _ _ η _)
    abstract !fn_n_distrib⁻¹ ⬝ ap (λx, G ∘fn x) (@left_inverse  (C ⇒ D) _ _ _ η _)  ⬝ !fn_id end
    abstract !fn_n_distrib⁻¹ ⬝ ap (λx, G ∘fn x) (@right_inverse (C ⇒ D) _ _ _ η _) ⬝ !fn_id end

  definition is_iso_fn_compose [constructor] (η : G ⟹ G') (F : C ⇒ D) [H : is_iso η]
    : is_iso (η ∘nf F) :=
  is_iso.mk
    (@inverse (D ⇒ E) _ _ _ η _ ∘nf F)
    abstract !n_nf_distrib⁻¹ ⬝ ap (λx, x ∘nf F) (@left_inverse  (D ⇒ E) _ _ _ η _)  ⬝ !id_nf end
    abstract !n_nf_distrib⁻¹ ⬝ ap (λx, x ∘nf F) (@right_inverse (D ⇒ E) _ _ _ η _)  ⬝ !id_nf end

  definition functor_iso_compose [constructor] (G : D ⇒ E) (η : F ≅ F') : G ∘f F ≅ G ∘f F' :=
  iso.mk _ (is_iso_nf_compose G (to_hom η))

  definition iso_functor_compose [constructor] (η : G ≅ G') (F : C ⇒ D) : G ∘f F ≅ G' ∘f F :=
  iso.mk _ (is_iso_fn_compose (to_hom η) F)

  infixr ` ∘fi ` :62 := functor_iso_compose
  infixr ` ∘if ` :62 := iso_functor_compose


/- TODO: also needs n_nf_distrib and id_nf for these compositions
  definition nidf_compose [constructor] (η : J ⟹ 1) (F : C ⇒ D) [H : is_iso η]
    : is_iso (η ∘n1f F) :=
  is_iso.mk
   (@inverse (D ⇒ D) _ _ _ η _ ∘1nf F)
   abstract _ end
            _

  definition idnf_compose [constructor] (η : 1 ⟹ J) (F : C ⇒ D) [H : is_iso η]
    : is_iso (η ∘1nf F) :=
  is_iso.mk _
            _
            _

  definition fnid_compose [constructor] (F : D ⇒ E) (η : J ⟹ 1) [H : is_iso η]
    : is_iso (F ∘fn1 η) :=
  is_iso.mk _
            _
            _

  definition fidn_compose [constructor] (F : D ⇒ E) (η : 1 ⟹ J) [H : is_iso η]
    : is_iso (F ∘f1n η) :=
  is_iso.mk _
            _
            _
-/

  end

  namespace functor

    variables {C : Precategory} {D : Category} {F G : D ^c C}
    definition eq_of_iso_ob (η : F ≅ G) (c : C) : F c = G c :=
    by apply eq_of_iso; apply componentwise_iso; exact η

    local attribute functor.to_fun_hom [reducible]
    definition eq_of_iso (η : F ≅ G) : F = G :=
    begin
    fapply functor_eq,
      {exact (eq_of_iso_ob η)},
      {intro c c' f,
        esimp [eq_of_iso_ob, inv_of_eq, hom_of_eq, eq_of_iso],
        rewrite [*right_inv iso_of_eq],
        symmetry, apply @naturality_iso _ _ _ _ _ (iso.struct _)
      }
    end

    definition iso_of_eq_eq_of_iso (η : F ≅ G) : iso_of_eq (eq_of_iso η) = η :=
    begin
    apply iso_eq,
    apply nat_trans_eq,
    intro c,
    rewrite natural_map_hom_of_eq, esimp [eq_of_iso],
    rewrite ap010_functor_eq, esimp [hom_of_eq,eq_of_iso_ob],
    rewrite (right_inv iso_of_eq),
    end

    definition eq_of_iso_iso_of_eq (p : F = G) : eq_of_iso (iso_of_eq p) = p :=
    begin
    apply functor_eq2,
    intro c,
    esimp [eq_of_iso],
    rewrite ap010_functor_eq,
    esimp [eq_of_iso_ob],
    rewrite componentwise_iso_iso_of_eq,
    rewrite (left_inv iso_of_eq)
    end

    definition is_univalent (D : Category) (C : Precategory) : is_univalent (D ^c C) :=
    λF G, adjointify _ eq_of_iso
                       iso_of_eq_eq_of_iso
                       eq_of_iso_iso_of_eq

  end functor

  definition category_functor [instance] [constructor] (D : Category) (C : Precategory)
    : category (D ^c C) :=
  category.mk (D ^c C) (functor.is_univalent D C)

  definition Category_functor [constructor] (D : Category) (C : Precategory) : Category :=
  category.Mk (D ^c C) !category_functor

  --this definition is only useful if the exponent is a category,
  --  and the elaborator has trouble with inserting the coercion
  definition Category_functor' [constructor] (D C : Category) : Category :=
  Category_functor D C

  namespace ops
    infixr ` ^c2 `:35 := Category_functor
  end ops

  namespace functor
    variables {C : Precategory} {D : Category} {F G : D ^c C}

    definition eq_of_pointwise_iso (η : F ⟹ G) (iso : Π(a : C), is_iso (η a)) : F = G :=
    eq_of_iso (natural_iso.mk η iso)

   definition iso_of_eq_eq_of_pointwise_iso (η : F ⟹ G) (iso : Π(c : C), is_iso (η c))
      : iso_of_eq (eq_of_pointwise_iso η iso) = natural_iso.mk η iso :=
   !iso_of_eq_eq_of_iso

   definition hom_of_eq_eq_of_pointwise_iso (η : F ⟹ G) (iso : Π(c : C), is_iso (η c))
      : hom_of_eq (eq_of_pointwise_iso η iso) = η :=
   !hom_of_eq_eq_of_iso

   definition inv_of_eq_eq_of_pointwise_iso (η : F ⟹ G) (iso : Π(c : C), is_iso (η c))
      : inv_of_eq (eq_of_pointwise_iso η iso) = nat_trans_inverse η :=
   !inv_of_eq_eq_of_iso

  end functor

  /-
    functors involving only the functor category
    (see ..functor.curry for some other functors involving also products)
  -/

  variables {C D I : Precategory}
  definition constant2_functor [constructor] (F : I ⇒ D ^c C) (c : C) : I ⇒ D :=
  functor.mk (λi, to_fun_ob (F i) c)
             (λi j f, natural_map (F f) c)
             abstract (λi, ap010 natural_map !respect_id c ⬝ proof idp qed) end
             abstract (λi j k g f, ap010 natural_map !respect_comp c) end

  definition constant2_functor_natural [constructor] (F : I ⇒ D ^c C) {c d : C} (f : c ⟶ d)
    : constant2_functor F c ⟹ constant2_functor F d :=
  nat_trans.mk (λi, to_fun_hom (F i) f)
               (λi j k, (naturality (F k) f)⁻¹)

  definition functor_flip [constructor] (F : I ⇒ D ^c C) : C ⇒ D ^c I :=
  functor.mk (constant2_functor F)
             @(constant2_functor_natural F)
             abstract begin intros, apply nat_trans_eq, intro i, esimp, apply respect_id end end
             abstract begin intros, apply nat_trans_eq, intro i, esimp, apply respect_comp end end

  definition eval_functor [constructor] (C D : Precategory) (d : D) : C ^c D ⇒ C :=
  begin
    fapply functor.mk: esimp,
    { intro F, exact F d},
    { intro G F η, exact η d},
    { intro F, reflexivity},
    { intro H G F η θ, reflexivity},
  end

  definition precomposition_functor [constructor] {C D} (E) (F : C ⇒ D)
    : E ^c D ⇒ E ^c C :=
  begin
    fapply functor.mk: esimp,
    { intro G, exact G ∘f F},
    { intro G H η, exact η ∘nf F},
    { intro G, reflexivity},
    { intro G H I η θ, reflexivity},
  end

  definition faithful_precomposition_functor [instance] 
    {C D E} {H : C ⇒ D} [Hs : essentially_surjective H] : faithful (precomposition_functor E H) :=
  begin
    intro F G γ δ Hγδ, apply nat_trans_eq, intro b,
    induction Hs b with Hb, induction Hb with a f,
    refine naturality_iso_right γ f ⬝ _ ⬝ (naturality_iso_right δ f)⁻¹,
    apply ap (λ x, _ ∘ natural_map x a ∘ _) Hγδ,
  end

  open sigma sigma.ops
  section fully_faithful_precomposition
  variables {E : Precategory} {H : C ⇒ D} [Hs : essentially_surjective H] [Hf : full H]
    {F G : D ⇒ E} (γ : F ∘f H ⟹ G ∘f H)
  include Hs Hf

  private definition fully_faithful_precomposition_functor_prop [instance] (b) :
    is_prop (Σ g, Π a (f : H a ≅ b), γ a = G f⁻¹ⁱ ∘ g ∘ F f) :=
  begin
    fapply is_prop.mk, intros g h, cases g with g Hg, cases h with h Hh,
    fapply sigma.dpair_eq_dpair,
    { induction Hs b with Hb, induction Hb with a0 f,
      apply comp.cancel_right (F f), apply comp.cancel_left (G f⁻¹ⁱ),
      apply (Hg a0 f)⁻¹ ⬝ (Hh a0 f) },
    apply is_prop.elimo
  end

  private definition fully_faithful_precomposition_functor_pair [reducible] (b) :
    Σ g, Π a (f : H a ≅ b), γ a = G f⁻¹ⁱ ∘ g ∘ F f :=
  begin
    induction Hs b with Hb, induction Hb with a0 h, fconstructor,
    exact G h ∘ γ a0 ∘ F h⁻¹ⁱ, intro a f,
    induction Hf (to_hom (f ⬝i h⁻¹ⁱ)) with k Ek, 
    have is_iso (H k), by rewrite Ek; apply _,
    refine _ ⬝ !assoc⁻¹, refine _ ⬝ ap (λ x, x ∘ F f) !assoc⁻¹, refine _ ⬝ !assoc,
    refine _ ⬝ ap (λ x, (G f⁻¹ⁱ ∘ G h) ∘ x) !assoc,
    do 2 krewrite [-respect_comp], esimp,
    apply eq_comp_of_inverse_comp_eq,
    exact ap (λ x, G x ∘ γ a) Ek⁻¹ ⬝ naturality γ k ⬝ ap (λ x, γ a0 ∘ F x) Ek
  end

  --TODO speed this up
  private definition fully_faithful_precomposition_naturality {b b' : carrier D}
    (f : hom b b') : to_fun_hom G f ∘ (fully_faithful_precomposition_functor_pair γ b).1 
    = (fully_faithful_precomposition_functor_pair γ b').1 ∘ to_fun_hom F f :=
  begin
    esimp[fully_faithful_precomposition_functor_pair],
    induction Hs b with Hb, induction Hb with a h,
    induction Hs b' with Hb', induction Hb' with a' h',
    induction Hf (to_hom h'⁻¹ⁱ ∘ f ∘ to_hom h) with k Ek, 
    apply concat, apply assoc,
    apply concat, apply ap (λ x, x ∘ _),
     apply concat, apply !respect_comp⁻¹, 
     apply concat, apply ap (λ x, to_fun_hom G x), apply inverse, 
      apply comp_eq_of_eq_inverse_comp, apply Ek, apply respect_comp,
    apply concat, apply !assoc⁻¹, 
    apply concat, apply ap (λ x, _ ∘ x), apply concat, apply assoc, 
     apply concat, apply ap (λ x, x ∘ _), apply naturality γ, apply !assoc⁻¹, 
    apply concat, apply ap (λ x, _ ∘ _ ∘ x), apply concat, esimp, apply !respect_comp⁻¹, 
     apply concat, apply ap (λ x, to_fun_hom F x), 
      apply comp_inverse_eq_of_eq_comp, apply Ek ⬝ !assoc, apply respect_comp, 
    apply concat, apply assoc, apply concat, apply assoc,
    apply ap (λ x, x ∘ _) !assoc⁻¹
  end

  definition fully_faithful_precomposition_functor [instance] :
    fully_faithful (precomposition_functor E H) :=
  begin
    apply fully_faithful_of_full_of_faithful,
    { apply faithful_precomposition_functor },
    { intro F G γ, esimp at *, fapply image.mk,
      fconstructor,
      { intro b, apply (fully_faithful_precomposition_functor_pair γ b).1 }, 
      { intro b b' f, apply fully_faithful_precomposition_naturality },
      { fapply nat_trans_eq, intro a, esimp,
        apply inverse,
        induction (fully_faithful_precomposition_functor_pair γ (to_fun_ob H a)) with g Hg,
        esimp, apply concat, apply Hg a (iso.refl (H a)), esimp,
        apply concat, apply ap (λ x, x ∘ _), apply respect_id, apply concat, apply id_left, 
        apply concat, apply ap (λ x, _ ∘ x), apply respect_id, apply id_right } }
  end

  end fully_faithful_precomposition

end functor

namespace functor

  section essentially_surjective_precomposition

  parameters {A B : Precategory} {C : Category}
    {H : A ⇒ B} [He : is_weak_equivalence H] (F : A ⇒ C)
  variables {b b' : carrier B} (f : hom b b')
  include A B C H He F

  structure essentially_surj_precomp_X (b : carrier B) : Type :=
    (c : carrier C)
    (k : Π (a : carrier A) (h : H a ≅ b), F a ≅ c)
    (k_coh : Π {a a'} h h' (f : hom a a'), to_hom h' ∘ (to_fun_hom H f) = to_hom h 
      → to_hom (k a' h') ∘ to_fun_hom F f = to_hom (k a h))
  local abbreviation X := essentially_surj_precomp_X
  local abbreviation X.mk [constructor] := @essentially_surj_precomp_X.mk
  local abbreviation X.c [unfold 7] := @essentially_surj_precomp_X.c
  local abbreviation X.k [unfold 7] := @essentially_surj_precomp_X.k
  local abbreviation X.k_coh [unfold 7] :=  @essentially_surj_precomp_X.k_coh

  section
  variables {c c' : carrier C} (p : c = c')
    {k : Π (a : carrier A) (h : H a ≅ b), F a ≅ c}
    {k' : Π (a : carrier A) (h : H a ≅ b), F a ≅ c'}
    (q : Π (a : carrier A) (h : H a ≅ b), to_hom (k a h ⬝i iso_of_eq p) = to_hom (k' a h))
    {k_coh : Π {a a'} h h' (f : hom a a'), to_hom h' ∘ (to_fun_hom H f) = to_hom h 
      → to_hom (k a' h') ∘ to_fun_hom F f = to_hom (k a h)}
    {k'_coh : Π {a a'} h h' (f : hom a a'), to_hom h' ∘ (to_fun_hom H f) = to_hom h 
      → to_hom (k' a' h') ∘ to_fun_hom F f = to_hom (k' a h)}
  include c c' p k k' q

  private theorem X_eq : X.mk c k @k_coh = X.mk c' k' @k'_coh :=
  begin
    cases p,
    assert q' : k = k',
    { apply eq_of_homotopy, intro a, apply eq_of_homotopy, intro h, 
      apply iso_eq, apply !id_left⁻¹ ⬝ q a h },
    cases q',
    apply ap (essentially_surj_precomp_X.mk c' k'),
    apply is_prop.elim
  end

  end

  open prod.ops sigma.ops
  private theorem X_prop [instance] : is_prop (X b) :=
  begin
    induction He.2 b with Hb, cases Hb with a0 Ha0,
    fapply is_prop.mk, intros f g, cases f with cf kf kf_coh, cases g with cg kg kg_coh,
    fapply X_eq,
    { apply eq_of_iso, apply iso.trans, apply iso.symm, apply kf a0 Ha0,
      apply kg a0 Ha0 },
    { intro a h,
      assert fHf : Σ f : hom a a0, to_hom Ha0 ∘ (to_fun_hom H f) = to_hom h,
      { fconstructor, apply hom_inv, apply He.1, exact to_hom Ha0⁻¹ⁱ ∘ to_hom h,
        apply concat, apply ap (λ x, _ ∘ x), apply right_inv (to_fun_hom H),
        apply comp_inverse_cancel_left },
      apply concat, apply ap (λ x, to_hom x ∘ _), apply iso_of_eq_eq_of_iso,
      apply concat, apply ap (λ x, _ ∘ x), apply (kf_coh h Ha0 fHf.1 fHf.2)⁻¹,
      apply concat, rotate 1, apply kg_coh h Ha0 fHf.1 fHf.2,
      apply concat, apply assoc, apply ap (λ x, x ∘ _),
      apply concat, apply !assoc⁻¹,
      apply concat, apply ap (λ x, _ ∘ x), apply comp.left_inverse,
      apply id_right },
  end

  private definition X_inh (b) : X b :=
  begin
    induction He.2 b with Hb, cases Hb with a0 Ha0,
    fconstructor, exact F a0,
    { intro a h, apply to_fun_iso F, apply reflect_iso H,
      exact h ⬝i Ha0⁻¹ⁱ },
    { intros a a' h h' f HH,
      apply concat, apply !respect_comp⁻¹, apply ap (to_fun_hom F), 
      esimp, rewrite [-HH],
      apply concat, apply ap (λ x, _ ∘ x), apply inverse, apply left_inv (to_fun_hom H), 
      apply concat, apply !hom_inv_respect_comp⁻¹, apply ap (hom_inv H), 
      apply !assoc⁻¹ }
  end
  local abbreviation G0 [reducible] := λ (b), X.c (X_inh b)
  private definition k := λ b, X.k (X_inh b)
  private definition k_coh := λ b, @X.k_coh b (X_inh b)

  private definition X_c_eq_of_eq {b} (t t' : X b) (p : t = t') : X.c t = X.c t' :=
  by cases p; reflexivity

  private definition X_k_eq_of_eq {b} (t t' : X b) (p : t = t') (a : carrier A) (h : H a ≅ b) :
    X_c_eq_of_eq t t' p ▸ X.k t a h = X.k t' a h:=
  by cases p; reflexivity

  private definition X_phi {b} (t : X b) : X.c t = X.c (X_inh b) :=
  X_c_eq_of_eq _ _ !is_prop.elim

  private definition X_phi_transp {b} (t : X b) (a : carrier A) (h : H a ≅ b) :
    (X_phi t) ▸ (X.k t a h) = k b a h :=
  by apply X_k_eq_of_eq t _ !is_prop.elim

  private definition X_phi_hom_of_eq' {b} (t t' : X b) (p : t = t') (a : carrier A) (h : H a ≅ b) :
    X.k t' a h ⬝i (iso_of_eq (X_c_eq_of_eq t t' p)⁻¹) = X.k t a h :=
  begin
    cases p, apply iso_eq, apply id_left
  end

  private definition X_phi_hom_of_eq {b} (t : X b) (a : carrier A) (h : H a ≅ b) :
    to_hom (k b a h ⬝i (iso_of_eq (X_phi t)⁻¹)) = to_hom (X.k t a h) :=
  begin
    apply ap to_hom, apply X_phi_hom_of_eq'
  end

  structure essentially_surj_precomp_Y {b b' : carrier B} (f : hom b b') : Type :=
    (g : hom (G0 b) (G0 b'))
    (Hg : Π {a a' : carrier A} h h' (l : hom a a'), to_hom h' ∘ to_fun_hom H l = f ∘ to_hom h →
      to_hom (k b' a' h') ∘ to_fun_hom F l = g ∘ to_hom (k b a h))
  local abbreviation Y := @essentially_surj_precomp_Y
  local abbreviation Y.mk := @essentially_surj_precomp_Y.mk
  local abbreviation Y.g := @essentially_surj_precomp_Y.g

  section
  variables {g : hom (G0 b) (G0 b')} {g' : hom (G0 b) (G0 b')} (p : g = g')
    (Hg : Π {a a' : carrier A} h h' (l : hom a a'), to_hom h' ∘ to_fun_hom H l = f ∘ to_hom h →
      to_hom (k b' a' h') ∘ to_fun_hom F l = g ∘ to_hom (k b a h))
    (Hg' : Π {a a' : carrier A} h h' (l : hom a a'), to_hom h' ∘ to_fun_hom H l = f ∘ to_hom h →
      to_hom (k b' a' h') ∘ to_fun_hom F l = g' ∘ to_hom (k b a h))
  include p

  private theorem Y_eq : Y.mk g @Hg = Y.mk g' @Hg' :=
  begin
    cases p, apply ap (Y.mk g'),
    apply is_prop.elim,
  end

  end

  private theorem Y_prop [instance] : is_prop (Y f) :=
  begin
    induction He.2 b with Hb, cases Hb with a0 h0,
    induction He.2 b' with Hb', cases Hb' with a0' h0',
    fapply is_prop.mk, intros,
    cases x with g0 Hg0, cases y with g1 Hg1,
    apply Y_eq,
    assert l0Hl0 : Σ l0 : hom a0 a0', to_hom h0' ∘ to_fun_hom H l0 = f ∘ to_hom h0,
    { fconstructor, apply hom_inv, apply He.1, exact to_hom h0'⁻¹ⁱ ∘ f ∘ to_hom h0,
      apply concat, apply ap (λ x, _ ∘ x), apply right_inv (to_fun_hom H),
      apply comp_inverse_cancel_left },
    apply comp.cancel_right (to_hom (k b a0 h0)),
    apply concat, apply inverse, apply Hg0 h0 h0' l0Hl0.1 l0Hl0.2,
    apply Hg1 h0 h0' l0Hl0.1 l0Hl0.2
  end

  private definition Y_inh : Y f :=
  begin
    induction He.2 b with Hb, cases Hb with a0 h0,
    induction He.2 b' with Hb', cases Hb' with a0' h0',
    assert l0Hl0 : Σ l0 : hom a0 a0', to_hom h0' ∘ to_fun_hom H l0 = f ∘ to_hom h0,
    { fconstructor, apply hom_inv, apply He.1, exact to_hom h0'⁻¹ⁱ ∘ f ∘ to_hom h0,
      apply concat, apply ap (λ x, _ ∘ x), apply right_inv (to_fun_hom H),
      apply comp_inverse_cancel_left },
    fapply Y.mk,
    { refine to_hom (k b' a0' h0') ∘ _ ∘ to_hom (k b a0 h0)⁻¹ⁱ, 
      apply to_fun_hom F, apply l0Hl0.1 },
    { intros a a' h h' l Hl, esimp, apply inverse,
      assert mHm : Σ m, to_hom h0 ∘ to_fun_hom H m = to_hom h,
      { fconstructor, apply hom_inv, apply He.1, exact to_hom h0⁻¹ⁱ ∘ to_hom h, 
        apply concat, apply ap (λ x, _ ∘ x), apply right_inv (to_fun_hom H),
        apply comp_inverse_cancel_left },
      assert m'Hm' : Σ m', to_hom h0' ∘ to_fun_hom H m' = to_hom h',
      { fconstructor, apply hom_inv, apply He.1, exact to_hom h0'⁻¹ⁱ ∘ to_hom h', 
        apply concat, apply ap (λ x, _ ∘ x), apply right_inv (to_fun_hom H),
        apply comp_inverse_cancel_left },
      assert m'l0lm : l0Hl0.1 ∘ mHm.1 = m'Hm'.1 ∘ l,
      { apply faithful_of_fully_faithful, apply He.1,
        apply concat, apply respect_comp, apply comp.cancel_left (to_hom h0'), apply inverse,
        apply concat, apply ap (λ x, _ ∘ x), apply respect_comp, 
        apply concat, apply assoc,
        apply concat, apply ap (λ x, x ∘ _), apply m'Hm'.2,
        apply concat, apply Hl, 
        apply concat, apply ap (λ x, _ ∘ x), apply mHm.2⁻¹,
        apply concat, apply assoc,
        apply concat, apply ap (λ x, x ∘ _), apply l0Hl0.2⁻¹, apply !assoc⁻¹ },
      apply concat, apply !assoc⁻¹,
      apply concat, apply ap (λ x, _ ∘ x), apply !assoc⁻¹, 
      apply concat, apply ap (λ x, _ ∘ _ ∘ x), apply inverse_comp_eq_of_eq_comp, 
       apply inverse, apply k_coh b h h0, apply mHm.2,
      apply concat, apply ap (λ x, _ ∘ x), apply concat, apply !respect_comp⁻¹, 
       apply concat, apply ap (to_fun_hom F), apply m'l0lm, apply respect_comp,
      apply concat, apply assoc, apply ap (λ x, x ∘ _),
      apply k_coh, apply m'Hm'.2 }
  end
 
  private definition G_hom [constructor] := λ {b b'} (f : hom b b'), Y.g (Y_inh f)
  private definition G_hom_coh := λ {b b'} (f : hom b b'),
    @essentially_surj_precomp_Y.Hg b b' f (Y_inh f)

  private theorem G_hom_id (b : carrier B) : G_hom (ID b) = ID (G0 b) :=
  begin
    cases He with He1 He2, esimp[G_hom, Y_inh],
    induction He2 b with Hb, cases Hb with a h, --why do i need to destruct He?
    apply concat, apply ap (λ x, _ ∘ x ∘ _),
     apply concat, apply ap (to_fun_hom F),
      apply concat, apply ap (hom_inv H), apply inverse_comp_id_comp,
      apply hom_inv_respect_id,
     apply respect_id,
    apply comp_id_comp_inverse
  end

  private theorem G_hom_comp {b0 b1 b2 : carrier B} (g : hom b1 b2) (f : hom b0 b1) :
    G_hom (g ∘ f) = G_hom g ∘ G_hom f :=
  begin
    cases He with He1 He2, esimp[G_hom, Y_inh],
    induction He2 b0 with Hb0, cases Hb0 with a0 h0,
    induction He2 b1 with Hb1, cases Hb1 with a1 h1,
    induction He2 b2 with Hb2, cases Hb2 with b2 h2,
    apply concat, apply assoc,
    apply concat, rotate 1, apply !assoc⁻¹,
    apply concat, rotate 1, apply !assoc⁻¹,
    apply ap (λ x, x ∘ _),
    apply inverse, apply concat, apply ap (λ x, x ∘ _),
     apply concat, apply !assoc⁻¹, apply ap (λ x, _ ∘ x),
     apply concat, apply !assoc⁻¹, apply ap (λ x, _ ∘ x), apply comp.left_inverse,
    apply concat, apply !assoc⁻¹, apply ap (λ x, _ ∘ x),
    apply concat, apply ap (λ x, x ∘ _), apply id_right,
    apply concat, apply !respect_comp⁻¹, apply ap (to_fun_hom F),
    apply concat, apply !hom_inv_respect_comp⁻¹, apply ap (hom_inv H),
    apply concat, apply ap (λ x, x ∘ _), apply assoc,
    apply concat, apply assoc,
    apply concat, apply ap (λ x, x ∘ _), apply comp_inverse_cancel_right,
    apply concat, apply !assoc⁻¹, apply ap (λ x, _ ∘ x),
    apply assoc,
  end

  private definition G_functor : B ⇒ C :=
  begin
    fconstructor,
    { exact G0 },
    { intro b b' f, exact G_hom f },
    { intro b, apply G_hom_id },
    { intro a b c g f, apply G_hom_comp }
  end

  private definition XF (a0 : carrier A) : X (H a0) :=
  begin
    fconstructor,
    { exact F a0 },
    { intro a h, apply to_fun_iso F, apply reflect_iso, apply He.1, exact h },
    { intro a a' h h' f l, esimp, 
      apply concat, apply !respect_comp⁻¹, apply ap (to_fun_hom F), apply inverse,
      apply concat, apply ap (hom_inv H) l⁻¹,
      apply concat, apply hom_inv_respect_comp, apply ap (λ x, _ ∘ x), apply left_inv }
  end

  private definition G0_H_eq_F (a0 : carrier A) : G0 (H a0) = F a0 :=
  begin
    apply inverse, apply X_phi (XF a0)
  end

  private theorem G_hom_H_eq_F {a0 a0' : carrier A} (f0 : hom a0 a0') :
    hom_of_eq (G0_H_eq_F a0') ∘ G_hom (to_fun_hom H f0) ∘ inv_of_eq (G0_H_eq_F a0)
    = to_fun_hom F f0 :=
  begin
    apply comp_eq_of_eq_inverse_comp, apply comp_inverse_eq_of_eq_comp,
    apply concat, apply ap essentially_surj_precomp_Y.g, apply is_prop.elim,
    fconstructor,
    { exact (inv_of_eq (G0_H_eq_F a0') ∘ to_fun_hom F f0) ∘ hom_of_eq (G0_H_eq_F a0) },
    { intros a a' h h' l α, esimp[G0_H_eq_F], apply inverse,
      apply concat, apply !assoc⁻¹,
      apply concat, apply ap (λ x, _ ∘ x), apply X_phi_hom_of_eq,
      apply concat, apply !assoc⁻¹,
      apply inverse_comp_eq_of_eq_comp, apply inverse,
      apply concat, apply assoc,
      apply concat, apply ap (λ x, x ∘ _), apply X_phi_hom_of_eq, esimp[XF],
      refine !respect_comp⁻¹ ⬝ ap (to_fun_hom F) _ ⬝ !respect_comp,
      apply eq_of_fn_eq_fn' (to_fun_hom H),
      refine !respect_comp ⬝ _ ⬝ !respect_comp⁻¹,
      apply concat, apply ap (λ x, x ∘ _) !(right_inv (to_fun_hom H)),
      apply concat, rotate 1, apply ap (λ x, _ ∘ x) !(right_inv (to_fun_hom H))⁻¹,
      exact α },
    reflexivity
  end

  end essentially_surjective_precomposition

  definition essentially_surjective_precomposition_functor [instance] {A B : Precategory}
    (C : Category) (H : A ⇒ B) [He : is_weak_equivalence H] :
    essentially_surjective (precomposition_functor C H) :=
  begin
    intro F, apply tr, fconstructor, apply G_functor F,
    apply iso_of_eq, fapply functor_eq,
    { intro a, esimp[G_functor], exact G0_H_eq_F F a },
    { intro a b f, exact G_hom_H_eq_F F f }
  end

  variables {C D E : Precategory}

  definition postcomposition_functor [constructor] {C D} (E) (F : C ⇒ D)
    : C ^c E ⇒ D ^c E :=
  begin
    fapply functor.mk: esimp,
    { intro G, exact F ∘f G},
    { intro G H η, exact F ∘fn η},
    { intro G, apply fn_id},
    { intro G H I η θ, apply fn_n_distrib},
  end

  definition constant_diagram [constructor] (C D) : C ⇒ C ^c D :=
  begin
    fapply functor.mk: esimp,
    { intro c, exact constant_functor D c},
    { intro c d f, exact constant_nat_trans D f},
    { intro c, fapply nat_trans_eq, reflexivity},
    { intro c d e g f, fapply nat_trans_eq, reflexivity},
  end

  definition opposite_functor_opposite_left [constructor] (C D : Precategory)
    : (C ^c D)ᵒᵖ ⇒ Cᵒᵖ ^c Dᵒᵖ :=
  begin
    fapply functor.mk: esimp,
    { exact opposite_functor},
    { intro F G, exact opposite_nat_trans},
    { intro F, apply nat_trans_eq, reflexivity},
    { intro u v w g f, apply nat_trans_eq, reflexivity}
  end

  definition opposite_functor_opposite_right [constructor] (C D : Precategory)
    : Cᵒᵖ ^c Dᵒᵖ ⇒ (C ^c D)ᵒᵖ :=
  begin
    fapply functor.mk: esimp,
    { exact opposite_functor_rev},
    { apply @opposite_rev_nat_trans},
    { intro F, apply nat_trans_eq, intro d, reflexivity},
    { intro F G H η θ, apply nat_trans_eq, intro d, reflexivity}
  end

  definition constant_diagram_opposite [constructor] (C D)
    : (constant_diagram C D)ᵒᵖᶠ = opposite_functor_opposite_right C D ∘f constant_diagram Cᵒᵖ Dᵒᵖ :=
  begin
    fapply functor_eq,
    { reflexivity },
    { intro c c' f, esimp at *, refine !nat_trans.id_right ⬝ !nat_trans.id_left ⬝ _,
      apply nat_trans_eq, intro d, reflexivity }
  end

end functor
