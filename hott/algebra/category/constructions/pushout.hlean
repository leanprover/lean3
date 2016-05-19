/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

The pushout of categories

The morphisms in the pushout of two categories is defined as a quotient on lists of composable
morphisms. For this we use the notion of paths in a graph.
-/

import ..category ..nat_trans hit.set_quotient algebra.relation ..groupoid algebra.graph

open eq is_trunc functor trunc sum set_quotient relation iso category sigma nat

  /- we first define the categorical structure on paths in a graph -/
namespace paths
  section
  parameters {A : Type} {R : A → A → Type}
    (Q : Π⦃a a' : A⦄, paths R a a' → paths R a a' → Type)
  variables ⦃a a' a₁ a₂ a₃ a₄ : A⦄
  definition paths_trel [constructor] (l l' : paths R a a') : Prop :=
  ∥paths_rel Q l l'∥

  local notation `S` := @paths_trel
  definition paths_quotient (a a' : A) : Type := set_quotient (@S a a')
  local notation `mor` := paths_quotient
  local attribute paths_quotient [reducible]

  definition is_reflexive_R : is_reflexive (@S a a') :=
  begin constructor, intro s, apply tr, constructor end
  local attribute is_reflexive_R [instance]

  definition paths_compose [unfold 7 8] (g : mor a₂ a₃) (f : mor a₁ a₂) : mor a₁ a₃ :=
  begin
    refine quotient_binary_map _ _ g f, exact append,
    intros, refine trunc_functor2 _ r s, exact rel_respect_append
  end

  definition paths_id [constructor] (a : A) : mor a a :=
  class_of nil

  local infix ` ∘∘ `:60 := paths_compose
  local notation `p1` := paths_id _

  theorem paths_assoc (h : mor a₃ a₄) (g : mor a₂ a₃) (f : mor a₁ a₂) :
    h ∘∘ (g ∘∘ f) = (h ∘∘ g) ∘∘ f :=
  begin
    induction h using set_quotient.rec_prop with h,
    induction g using set_quotient.rec_prop with g,
    induction f using set_quotient.rec_prop with f,
    rewrite [▸*, append_assoc]
  end

  theorem paths_id_left (f : mor a a') : p1 ∘∘ f = f :=
  begin
    induction f using set_quotient.rec_prop with f,
    reflexivity
  end

  theorem paths_id_right (f : mor a a') : f ∘∘ p1 = f :=
  begin
    induction f using set_quotient.rec_prop with f,
    rewrite [▸*, append_nil]
  end

  definition Precategory_paths [constructor] : Precategory :=
  precategory.MK A
                 mor
                 _
                 paths_compose
                 paths_id
                 paths_assoc
                 paths_id_left
                 paths_id_right

  /- given a way to reverse edges and some additional properties we can extend this to a
    groupoid structure -/
  parameters (inv : Π⦃a a' : A⦄, R a a' → R a' a)
    (rel_inv : Π⦃a a' : A⦄ {l l' : paths R a a'},
      Q l l' → paths_rel Q (reverse inv l) (reverse inv l'))
    (li : Π⦃a a' : A⦄ (r : R a a'), paths_rel Q [inv r, r] nil)
    (ri : Π⦃a a' : A⦄ (r : R a a'), paths_rel Q [r, inv r] nil)

  include rel_inv li ri
  definition paths_inv [unfold 8] (f : mor a a') : mor a' a :=
  begin
    refine quotient_unary_map (reverse inv) _ f,
    intros, refine trunc_functor _ _ r, esimp,
    intro s, apply rel_respect_reverse inv s rel_inv
  end

  local postfix `^`:max := paths_inv

  theorem paths_left_inv (f : mor a₁ a₂) : f^ ∘∘ f = p1 :=
  begin
    induction f using set_quotient.rec_prop with f,
    esimp, apply eq_of_rel, apply tr,
    apply rel_left_inv, apply li
  end

  theorem paths_right_inv (f : mor a₁ a₂) : f ∘∘ f^ = p1 :=
  begin
    induction f using set_quotient.rec_prop with f,
    esimp, apply eq_of_rel, apply tr,
    apply rel_right_inv, apply ri
  end

  definition Groupoid_paths [constructor] : Groupoid :=
  groupoid.MK Precategory_paths
    (λa b f, is_iso.mk (paths_inv f) (paths_left_inv f) (paths_right_inv f))

  end

end paths
open paths

namespace category

  /- We use this for the pushout of categories -/
  inductive pushout_prehom_index {C : Type} (D E : Precategory) (F : C → D) (G : C → E) :
    D + E → D + E → Type :=
  | iD : Π{d d' : D} (f : d ⟶ d'), pushout_prehom_index D E F G (inl d) (inl d')
  | iE : Π{e e' : E} (g : e ⟶ e'), pushout_prehom_index D E F G (inr e) (inr e')
  | DE : Π(c : C), pushout_prehom_index D E F G (inl (F c)) (inr (G c))
  | ED : Π(c : C), pushout_prehom_index D E F G (inr (G c)) (inl (F c))

  open pushout_prehom_index

  definition pushout_prehom {C : Type} (D E : Precategory) (F : C → D) (G : C → E) :
    D + E → D + E → Type :=
  paths (pushout_prehom_index D E F G)

  inductive pushout_hom_rel_index {C : Type} (D E : Precategory) (F : C → D) (G : C → E) :
    Π⦃x x' : D + E⦄, pushout_prehom D E F G x x' → pushout_prehom D E F G x x' → Type :=
  | DD  : Π{d₁ d₂ d₃ : D} (g : d₂ ⟶ d₃) (f : d₁ ⟶ d₂),
      pushout_hom_rel_index D E F G [iD F G g, iD F G f] [iD F G (g ∘ f)]
  | EE  : Π{e₁ e₂ e₃ : E} (g : e₂ ⟶ e₃) (f : e₁ ⟶ e₂),
      pushout_hom_rel_index D E F G [iE F G g, iE F G f] [iE F G (g ∘ f)]
  | DED : Π(c : C), pushout_hom_rel_index D E F G [ED F G c, DE F G c] nil
  | EDE : Π(c : C), pushout_hom_rel_index D E F G [DE F G c, ED F G c] nil
  | idD : Π(d : D), pushout_hom_rel_index D E F G [iD F G (ID d)] nil
  | idE : Π(e : E), pushout_hom_rel_index D E F G [iE F G (ID e)] nil

  open pushout_hom_rel_index

  definition Precategory_pushout [constructor] {C : Type} (D E : Precategory)
    (F : C → D) (G : C → E) : Precategory :=
  Precategory_paths (pushout_hom_rel_index D E F G)

  /- We can also take the pushout of groupoids -/

  variables {C : Type} (D E : Groupoid) (F : C → D) (G : C → E)
  variables ⦃x x' x₁ x₂ x₃ x₄ : Precategory_pushout D E F G⦄

  definition pushout_index_inv [unfold 8] (i : pushout_prehom_index D E F G x x') :
    pushout_prehom_index D E F G x' x :=
  begin
    induction i,
    { exact iD F G f⁻¹},
    { exact iE F G g⁻¹},
    { exact ED F G c},
    { exact DE F G c},
  end

  open paths.paths_rel
  theorem pushout_index_reverse {l l' : pushout_prehom D E F G x x'}
    (q : pushout_hom_rel_index D E F G l l') : paths_rel (pushout_hom_rel_index D E F G)
      (reverse (pushout_index_inv D E F G) l) (reverse (pushout_index_inv D E F G) l') :=
  begin
    induction q: apply paths_rel_of_Q;
    try rewrite reverse_singleton; try rewrite reverse_pair; try rewrite reverse_nil; esimp;
    try rewrite [comp_inverse]; try rewrite [id_inverse]; constructor,
  end

  theorem pushout_index_li (i : pushout_prehom_index D E F G x x') :
    paths_rel (pushout_hom_rel_index D E F G) [pushout_index_inv D E F G i, i] nil :=
  begin
    induction i: esimp,
    { refine rtrans (paths_rel_of_Q !DD) _,
      rewrite [comp.left_inverse], exact paths_rel_of_Q !idD},
    { refine rtrans (paths_rel_of_Q !EE) _,
      rewrite [comp.left_inverse], exact paths_rel_of_Q !idE},
    { exact paths_rel_of_Q !DED},
    { exact paths_rel_of_Q !EDE}
  end

  theorem pushout_index_ri (i : pushout_prehom_index D E F G x x') :
    paths_rel (pushout_hom_rel_index D E F G) [i, pushout_index_inv D E F G i] nil :=
  begin
    induction i: esimp,
    { refine rtrans (paths_rel_of_Q !DD) _,
      rewrite [comp.right_inverse], exact paths_rel_of_Q !idD},
    { refine rtrans (paths_rel_of_Q !EE) _,
      rewrite [comp.right_inverse], exact paths_rel_of_Q !idE},
    { exact paths_rel_of_Q !EDE},
    { exact paths_rel_of_Q !DED}
  end

  definition Groupoid_pushout [constructor] : Groupoid :=
  Groupoid_paths (pushout_hom_rel_index D E F G) (pushout_index_inv D E F G)
    (pushout_index_reverse D E F G) (pushout_index_li D E F G) (pushout_index_ri D E F G)


end category
