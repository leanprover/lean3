/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

The pushout of categories

The morphisms in the pushout of two categories is defined as a quotient on lists of composable
morphisms. We first define a general notion of indexed lists, such that each element in the list has two endpoints, and the endpoints between adjacent members of the list have to be the same.
-/

import ..category ..nat_trans hit.set_quotient algebra.relation ..groupoid

open eq is_trunc functor trunc sum set_quotient relation iso category sigma nat

inductive indexed_list {A : Type} (R : A → A → Type) : A → A → Type :=
| nil {} : Π{a : A}, indexed_list R a a
| cons   : Π{a₁ a₂ a₃ : A} (r : R a₂ a₃), indexed_list R a₁ a₂ → indexed_list R a₁ a₃

namespace indexed_list

  notation h :: t  := cons h t
  notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

  variables {A : Type} {R : A → A → Type} {a a' a₁ a₂ a₃ a₄ : A}

  definition concat (r : R a₁ a₂) (l : indexed_list R a₂ a₃) : indexed_list R a₁ a₃ :=
  begin
    induction l with a a₂ a₃ a₄ r' l IH,
    { exact [r]},
    { exact r' :: IH r}
  end

  theorem concat_nil (r : R a₁ a₂) : concat r (@nil A R a₂) = [r] := idp

  theorem concat_cons (r : R a₁ a₂) (r' : R a₃ a₄) (l : indexed_list R a₂ a₃)
    : concat r (r'::l)  = r'::(concat r l) := idp

  definition append (l₂ : indexed_list R a₂ a₃) (l₁ : indexed_list R a₁ a₂) :
    indexed_list R a₁ a₃ :=
  begin
    induction l₂,
    { exact l₁},
    { exact cons r (v_0 l₁)}
  end

  infix ` ++ ` := append

  definition nil_append (l : indexed_list R a₁ a₂) : nil ++ l = l := idp
  definition cons_append (r : R a₃ a₄) (l₂ : indexed_list R a₂ a₃) (l₁ : indexed_list R a₁ a₂) :
    (r :: l₂) ++ l₁ = r :: (l₂ ++ l₁) := idp

  definition singleton_append (r : R a₂ a₃) (l : indexed_list R a₁ a₂) : [r] ++ l = r :: l := idp
  definition append_singleton (l : indexed_list R a₂ a₃) (r : R a₁ a₂) : l ++ [r] = concat r l :=
  begin
    induction l,
    { reflexivity},
    { exact ap (cons r) !v_0}
  end

  definition append_nil (l : indexed_list R a₁ a₂) : l ++ nil = l :=
  begin
    induction l,
    { reflexivity},
    { exact ap (cons r) v_0}
  end

  definition append_assoc (l₃ : indexed_list R a₃ a₄) (l₂ : indexed_list R a₂ a₃)
    (l₁ : indexed_list R a₁ a₂) : (l₃ ++ l₂) ++ l₁ = l₃ ++ (l₂ ++ l₁) :=
  begin
    induction l₃,
    { reflexivity},
    { refine ap (cons r) !v_0}
  end

  theorem append_concat (l₂ : indexed_list R a₃ a₄) (l₁ : indexed_list R a₂ a₃) (r : R a₁ a₂) :
    l₂ ++ concat r l₁ = concat r (l₂ ++ l₁) :=
  begin
    induction l₂,
    { reflexivity},
    { exact ap (cons r_1) !v_0}
  end

  theorem concat_append (l₂ : indexed_list R a₃ a₄) (r : R a₂ a₃) (l₁ : indexed_list R a₁ a₂) :
    concat r l₂ ++ l₁ = l₂ ++ r :: l₁ :=
  begin
    induction l₂,
    { reflexivity},
    { exact ap (cons r) !v_0}
  end

  definition indexed_list.rec_tail {C : Π⦃a a' : A⦄, indexed_list R a a' → Type}
  (H0 : Π {a : A}, @C a a nil)
  (H1 : Π {a₁ a₂ a₃ : A} (r : R a₁ a₂) (l : indexed_list R a₂ a₃), C l → C (concat r l)) :
  Π{a a' : A} (l : indexed_list R a a'), C l :=
  begin
    have Π{a₁ a₂ a₃ : A} (l₂ : indexed_list R a₂ a₃) (l₁ : indexed_list R a₁ a₂) (c : C l₂),
      C (l₂ ++ l₁),
    begin
      intros, revert a₃ l₂ c, induction l₁: intros a₃ l₂ c,
      { rewrite append_nil, exact c},
      { rewrite [-concat_append], apply v_0, apply H1, exact c}
    end,
    intros, rewrite [-nil_append], apply this, apply H0
  end

  definition cons_eq_concat (r : R a₂ a₃) (l : indexed_list R a₁ a₂) :
    Σa (r' : R a₁ a) (l' : indexed_list R a a₃), r :: l = concat r' l' :=
  begin
    revert a₃ r, induction l: intros a₃' r',
    { exact ⟨a₃', r', nil, idp⟩},
    { cases (v_0 a₃ r) with a₄ w, cases w with r₂ w, cases w with l p, clear v_0,
      exact ⟨a₄, r₂, r' :: l, ap (cons r') p⟩}
  end

  definition length (l : indexed_list R a₁ a₂) : ℕ :=
  begin
    induction l,
    { exact 0},
    { exact succ v_0}
  end

  definition reverse (rev : Π⦃a a'⦄, R a a' → R a' a) (l : indexed_list R a₁ a₂) :
    indexed_list R a₂ a₁ :=
  begin
    induction l,
    { exact nil},
    { exact concat (rev r) v_0}
  end

  theorem reverse_nil (rev : Π⦃a a'⦄, R a a' → R a' a) : reverse rev (@nil A R a₁) = [] := idp

  theorem reverse_cons (rev : Π⦃a a'⦄, R a a' → R a' a) (r : R a₂ a₃) (l : indexed_list R a₁ a₂) :
    reverse rev (r::l) = concat (rev r) (reverse rev l) := idp

  theorem reverse_singleton (rev : Π⦃a a'⦄, R a a' → R a' a) (r : R a₁ a₂) :
    reverse rev [r] = [rev r] := idp

  theorem reverse_pair (rev : Π⦃a a'⦄, R a a' → R a' a) (r₂ : R a₂ a₃) (r₁ : R a₁ a₂) :
    reverse rev [r₂, r₁] = [rev r₁, rev r₂] := idp

  theorem reverse_concat (rev : Π⦃a a'⦄, R a a' → R a' a) (r : R a₁ a₂) (l : indexed_list R a₂ a₃) :
    reverse rev (concat r l) = rev r :: (reverse rev l) :=
  begin
    induction l,
    { reflexivity},
    { rewrite [concat_cons, reverse_cons, v_0]}
  end

  theorem reverse_append (rev : Π⦃a a'⦄, R a a' → R a' a) (l₂ : indexed_list R a₂ a₃)
    (l₁ : indexed_list R a₁ a₂) : reverse rev (l₂ ++ l₁) = reverse rev l₁ ++ reverse rev l₂ :=
  begin
    induction l₂,
    { exact !append_nil⁻¹},
    { rewrite [cons_append, +reverse_cons, append_concat, v_0]}
  end

  inductive indexed_list_rel {A : Type} {R : A → A → Type}
    (Q : Π⦃a a' : A⦄, indexed_list R a a' → indexed_list R a a' → Type)
    : Π⦃a a' : A⦄, indexed_list R a a' → indexed_list R a a' → Type :=
  | rrefl  : Π{a a' : A} (l : indexed_list R a a'), indexed_list_rel Q l l
  | rel    : Π{a₁ a₂ a₃ : A} {l₂ l₃ : indexed_list R a₂ a₃} (l : indexed_list R a₁ a₂) (q : Q l₂ l₃),
      indexed_list_rel Q (l₂ ++ l) (l₃ ++ l)
  | rcons  : Π{a₁ a₂ a₃ : A} {l₁ l₂ : indexed_list R a₁ a₂} (r : R a₂ a₃),
      indexed_list_rel Q l₁ l₂ → indexed_list_rel Q (cons r l₁) (cons r l₂)
  | rtrans : Π{a₁ a₂ : A} {l₁ l₂ l₃ : indexed_list R a₁ a₂},
      indexed_list_rel Q l₁ l₂ → indexed_list_rel Q l₂ l₃ → indexed_list_rel Q l₁ l₃

  open indexed_list_rel
  attribute rrefl [refl]
  attribute rtrans [trans]
  variables {Q : Π⦃a a' : A⦄, indexed_list R a a' → indexed_list R a a' → Type}

  definition indexed_list_rel_of_Q {l₁ l₂ : indexed_list R a₁ a₂} (q : Q l₁ l₂) :
    indexed_list_rel Q l₁ l₂ :=
  begin
    rewrite [-append_nil l₁, -append_nil l₂], exact rel nil q,
  end

  theorem rel_respect_append_left (l : indexed_list R a₂ a₃) {l₃ l₄ : indexed_list R a₁ a₂}
    (H : indexed_list_rel Q l₃ l₄) : indexed_list_rel Q (l ++ l₃) (l ++ l₄) :=
  begin
    induction l,
    { exact H},
    { exact rcons r (v_0 _ _ H)}
  end

  theorem rel_respect_append_right {l₁ l₂ : indexed_list R a₂ a₃} (l : indexed_list R a₁ a₂)
    (H₁ : indexed_list_rel Q l₁ l₂) : indexed_list_rel Q (l₁ ++ l) (l₂ ++ l) :=
  begin
    induction H₁ with a₁ a₂ l₁
                      a₂ a₃ a₄ l₂ l₂' l₁ q
                      a₂ a₃ a₄ l₁ l₂ r H₁ IH
                      a₂ a₃ l₁ l₂ l₂' H₁ H₁' IH IH',
    { reflexivity},
    { rewrite [+ append_assoc], exact rel _ q},
    { exact rcons r (IH l) },
    { exact rtrans (IH l) (IH' l)}
  end

  theorem rel_respect_append {l₁ l₂ : indexed_list R a₂ a₃} {l₃ l₄ : indexed_list R a₁ a₂}
    (H₁ : indexed_list_rel Q l₁ l₂) (H₂ : indexed_list_rel Q l₃ l₄) :
    indexed_list_rel Q (l₁ ++ l₃) (l₂ ++ l₄) :=
  begin
    induction H₁ with a₁ a₂ l
                      a₂ a₃ a₄ l₂ l₂' l q
                      a₂ a₃ a₄ l₁ l₂ r H₁ IH
                      a₂ a₃ l₁ l₂ l₂' H₁ H₁' IH IH',
    { exact rel_respect_append_left _ H₂},
    { rewrite [+ append_assoc], transitivity _, exact rel _ q,
      apply rel_respect_append_left, apply rel_respect_append_left, exact H₂},
    { exact rcons r (IH _ _ H₂) },
    { refine rtrans (IH _ _ H₂) _, apply rel_respect_append_right, exact H₁'}
  end

  theorem rel_respect_reverse (rev : Π⦃a a'⦄, R a a' → R a' a) {l₁ l₂ : indexed_list R a₁ a₂}
    (H : indexed_list_rel Q l₁ l₂)
    (rev_rel : Π⦃a a' : A⦄ {l l' : indexed_list R a a'},
      Q l l' → indexed_list_rel Q (reverse rev l) (reverse rev l')) :
    indexed_list_rel Q (reverse rev l₁) (reverse rev l₂) :=
  begin
    induction H,
    { reflexivity},
    { rewrite [+ reverse_append], apply rel_respect_append_left, apply rev_rel q},
    { rewrite [+reverse_cons,-+append_singleton], apply rel_respect_append_right, exact v_0},
    { exact rtrans v_0 v_1}
  end

  theorem rel_left_inv (rev : Π⦃a a'⦄, R a a' → R a' a) (l : indexed_list R a₁ a₂)
    (li : Π⦃a a' : A⦄ (r : R a a'), indexed_list_rel Q [rev r, r] nil) :
    indexed_list_rel Q (reverse rev l ++ l) nil :=
  begin
    induction l,
    { reflexivity},
    { rewrite [reverse_cons, concat_append],
      refine rtrans _ v_0, apply rel_respect_append_left,
      exact rel_respect_append_right _ (li r)}
  end

  theorem rel_right_inv (rev : Π⦃a a'⦄, R a a' → R a' a) (l : indexed_list R a₁ a₂)
    (ri : Π⦃a a' : A⦄ (r : R a a'), indexed_list_rel Q [r, rev r] nil) :
    indexed_list_rel Q (l ++ reverse rev l) nil :=
  begin
    induction l using indexed_list.rec_tail,
    { reflexivity},
    { rewrite [reverse_concat, concat_append],
      refine rtrans _ a, apply rel_respect_append_left,
      exact rel_respect_append_right _ (ri r)}
  end

end indexed_list
namespace indexed_list
  section
  parameters {A : Type} {R : A → A → Type}
    (Q : Π⦃a a' : A⦄, indexed_list R a a' → indexed_list R a a' → Type)
  variables ⦃a a' a₁ a₂ a₃ a₄ : A⦄
  definition indexed_list_trel [constructor] (l l' : indexed_list R a a') : Prop :=
  ∥indexed_list_rel Q l l'∥

  local notation `S` := @indexed_list_trel
  definition indexed_list_quotient (a a' : A) : Type := set_quotient (@S a a')
  local notation `mor` := indexed_list_quotient
  local attribute indexed_list_quotient [reducible]

  definition is_reflexive_R : is_reflexive (@S a a') :=
  begin constructor, intro s, apply tr, constructor end
  local attribute is_reflexive_R [instance]

  definition indexed_list_compose [unfold 7 8] (g : mor a₂ a₃) (f : mor a₁ a₂) : mor a₁ a₃ :=
  begin
    refine quotient_binary_map _ _ g f, exact append,
    intros, refine trunc_functor2 _ r s, exact rel_respect_append
  end

  definition indexed_list_id [constructor] (a : A) : mor a a :=
  class_of nil

  local infix ` ∘∘ `:60 := indexed_list_compose
  local notation `p1` := indexed_list_id _

  theorem indexed_list_assoc (h : mor a₃ a₄) (g : mor a₂ a₃) (f : mor a₁ a₂) :
    h ∘∘ (g ∘∘ f) = (h ∘∘ g) ∘∘ f :=
  begin
    induction h using set_quotient.rec_prop with h,
    induction g using set_quotient.rec_prop with g,
    induction f using set_quotient.rec_prop with f,
    rewrite [▸*, append_assoc]
  end

  theorem indexed_list_id_left (f : mor a a') : p1 ∘∘ f = f :=
  begin
    induction f using set_quotient.rec_prop with f,
    reflexivity
  end

  theorem indexed_list_id_right (f : mor a a') : f ∘∘ p1 = f :=
  begin
    induction f using set_quotient.rec_prop with f,
    rewrite [▸*, append_nil]
  end

  definition Precategory_indexed_list [constructor] : Precategory :=
  precategory.MK A
                 mor
                 _
                 indexed_list_compose
                 indexed_list_id
                 indexed_list_assoc
                 indexed_list_id_left
                 indexed_list_id_right

  parameters (inv : Π⦃a a' : A⦄, R a a' → R a' a)
    (rel_inv : Π⦃a a' : A⦄ {l l' : indexed_list R a a'},
      Q l l' → indexed_list_rel Q (reverse inv l) (reverse inv l'))
    (li : Π⦃a a' : A⦄ (r : R a a'), indexed_list_rel Q [inv r, r] nil)
    (ri : Π⦃a a' : A⦄ (r : R a a'), indexed_list_rel Q [r, inv r] nil)

  include rel_inv li ri
  definition indexed_list_inv [unfold 8] (f : mor a a') : mor a' a :=
  begin
    refine quotient_unary_map (reverse inv) _ f,
    intros, refine trunc_functor _ _ r, esimp,
    intro s, apply rel_respect_reverse inv s rel_inv
  end

  local postfix `^`:max := indexed_list_inv

  theorem indexed_list_left_inv (f : mor a₁ a₂) : f^ ∘∘ f = p1 :=
  begin
    induction f using set_quotient.rec_prop with f,
    esimp, apply eq_of_rel, apply tr,
    apply rel_left_inv, apply li
  end

  theorem indexed_list_right_inv (f : mor a₁ a₂) : f ∘∘ f^ = p1 :=
  begin
    induction f using set_quotient.rec_prop with f,
    esimp, apply eq_of_rel, apply tr,
    apply rel_right_inv, apply ri
  end

  definition Groupoid_indexed_list [constructor] : Groupoid :=
  groupoid.MK Precategory_indexed_list
    (λa b f, is_iso.mk (indexed_list_inv f) (indexed_list_left_inv f) (indexed_list_right_inv f))

  end



end indexed_list
open indexed_list

namespace category

  inductive pushout_prehom_index {C D E : Precategory} (F : C ⇒ D) (G : C ⇒ E) :
    D + E → D + E → Type :=
  | il : Π{d d' : D} (f : d ⟶ d'), pushout_prehom_index F G (inl d) (inl d')
  | ir : Π{e e' : E} (g : e ⟶ e'), pushout_prehom_index F G (inr e) (inr e')
  | lr : Π{c c' : C} (h : c ⟶ c'), pushout_prehom_index F G (inl (F c)) (inr (G c'))
  | rl : Π{c c' : C} (h : c ⟶ c'), pushout_prehom_index F G (inr (G c)) (inl (F c'))

  open pushout_prehom_index

  definition pushout_prehom {C D E : Precategory} (F : C ⇒ D) (G : C ⇒ E) : D + E → D + E → Type :=
  indexed_list (pushout_prehom_index F G)

  inductive pushout_hom_rel_index {C D E : Precategory} (F : C ⇒ D) (G : C ⇒ E) :
    Π⦃x x' : D + E⦄, pushout_prehom F G x x' → pushout_prehom F G x x' → Type :=
  | DD  : Π{d₁ d₂ d₃ : D} (g : d₂ ⟶ d₃) (f : d₁ ⟶ d₂),
      pushout_hom_rel_index F G [il F G g, il F G f] [il F G (g ∘ f)]
  | EE  : Π{e₁ e₂ e₃ : E} (g : e₂ ⟶ e₃) (f : e₁ ⟶ e₂),
      pushout_hom_rel_index F G [ir F G g, ir F G f] [ir F G (g ∘ f)]
  | DED : Π{c₁ c₂ c₃ : C} (g : c₂ ⟶ c₃) (f : c₁ ⟶ c₂),
      pushout_hom_rel_index F G [rl F G g, lr F G f] [il F G (to_fun_hom F (g ∘ f))]
  | EDE : Π{c₁ c₂ c₃ : C} (g : c₂ ⟶ c₃) (f : c₁ ⟶ c₂),
      pushout_hom_rel_index F G [lr F G g, rl F G f] [ir F G (to_fun_hom G (g ∘ f))]
  | idD : Π(d : D), pushout_hom_rel_index F G [il F G (ID d)] nil
  | idE : Π(e : E), pushout_hom_rel_index F G [ir F G (ID e)] nil

  open pushout_hom_rel_index
  -- section
  -- parameters {C D E : Precategory} (F : C ⇒ D) (G : C ⇒ E)
  -- local notation `ob` := D + E
  -- variables ⦃x x' x₁ x₂ x₃ x₄ : ob⦄

  -- definition pushout_hom_rel [constructor] (l l' : pushout_prehom F G x x') : Prop :=
  -- ∥indexed_list_rel (pushout_hom_rel_index F G) l l'∥

  -- local notation `R` := @pushout_hom_rel
  -- definition pushout_hom (x x' : ob) : Type := set_quotient (@R x x')
  -- local notation `mor` := @pushout_hom
  -- local attribute pushout_hom [reducible]

  -- definition is_reflexive_R : is_reflexive (@R x x') :=
  -- begin constructor, intro s, apply tr, constructor end
  -- local attribute is_reflexive_R [instance]

  -- definition pushout_compose [unfold 9 10] (g : mor x₂ x₃) (f : mor x₁ x₂) : mor x₁ x₃ :=
  -- begin
  --   refine quotient_binary_map _ _ g f, exact append,
  --   intros, refine trunc_functor2 _ r s, exact rel_respect_append
  -- end

  -- definition pushout_id [constructor] (x : ob) : mor x x :=
  -- class_of nil

  -- local infix ` ∘∘ `:60 := pushout_compose
  -- local notation `p1` := pushout_id _

  -- theorem pushout_assoc (h : mor x₃ x₄) (g : mor x₂ x₃) (f : mor x₁ x₂) :
  --   h ∘∘ (g ∘∘ f) = (h ∘∘ g) ∘∘ f :=
  -- begin
  --   induction h using set_quotient.rec_prop with h,
  --   induction g using set_quotient.rec_prop with g,
  --   induction f using set_quotient.rec_prop with f,
  --   rewrite [▸*, append_assoc]
  -- end

  -- theorem pushout_id_left (f : mor x x') : p1 ∘∘ f = f :=
  -- begin
  --   induction f using set_quotient.rec_prop with f,
  --   reflexivity
  -- end

  -- theorem pushout_id_right (f : mor x x') : f ∘∘ p1 = f :=
  -- begin
  --   induction f using set_quotient.rec_prop with f,
  --   rewrite [▸*, append_nil]
  -- end

  definition Precategory_pushout [constructor] {C D E : Precategory} (F : C ⇒ D) (G : C ⇒ E) :
    Precategory :=
  Precategory_indexed_list (pushout_hom_rel_index F G)
  -- precategory.MK ob
  --                mor
  --                _
  --                pushout_compose
  --                pushout_id
  --                pushout_assoc
  --                pushout_id_left
  --                pushout_id_right

  -- end

  variables {C D E : Groupoid} (F : C ⇒ D) (G : C ⇒ E)
  variables ⦃x x' x₁ x₂ x₃ x₄ : Precategory_pushout F G⦄

  definition pushout_index_inv [unfold 8] (i : pushout_prehom_index F G x x') :
    pushout_prehom_index F G x' x :=
  begin
    induction i,
    { exact il F G f⁻¹},
    { exact ir F G g⁻¹},
    { exact rl F G h⁻¹},
    { exact lr F G h⁻¹},
  end

  open indexed_list.indexed_list_rel
  theorem pushout_index_reverse {l l' : pushout_prehom F G x x'}
    (q : pushout_hom_rel_index F G l l') : indexed_list_rel (pushout_hom_rel_index F G)
      (reverse (pushout_index_inv F G) l) (reverse (pushout_index_inv F G) l') :=
  begin
    induction q: apply indexed_list_rel_of_Q; rewrite reverse_singleton; try rewrite reverse_pair;
    try rewrite reverse_nil; esimp,
    { rewrite [comp_inverse], constructor},
    { rewrite [comp_inverse], constructor},
    { rewrite [-respect_inv, comp_inverse], constructor},
    { rewrite [-respect_inv, comp_inverse], constructor},
    { rewrite [id_inverse], constructor},
    { rewrite [id_inverse], constructor}
  end

  theorem pushout_index_li (i : pushout_prehom_index F G x x') :
    indexed_list_rel (pushout_hom_rel_index F G) [pushout_index_inv F G i, i] nil :=
  begin
    induction i: esimp,
    { refine rtrans (indexed_list_rel_of_Q !DD) _,
      rewrite [comp.left_inverse], exact indexed_list_rel_of_Q !idD},
    { refine rtrans (indexed_list_rel_of_Q !EE) _,
      rewrite [comp.left_inverse], exact indexed_list_rel_of_Q !idE},
    { refine rtrans (indexed_list_rel_of_Q !DED) _,
      rewrite [comp.left_inverse, respect_id], exact indexed_list_rel_of_Q !idD},
    { refine rtrans (indexed_list_rel_of_Q !EDE) _,
      rewrite [comp.left_inverse, respect_id], exact indexed_list_rel_of_Q !idE}
  end

  theorem pushout_index_ri (i : pushout_prehom_index F G x x') :
    indexed_list_rel (pushout_hom_rel_index F G) [i, pushout_index_inv F G i] nil :=
  begin
    induction i: esimp,
    { refine rtrans (indexed_list_rel_of_Q !DD) _,
      rewrite [comp.right_inverse], exact indexed_list_rel_of_Q !idD},
    { refine rtrans (indexed_list_rel_of_Q !EE) _,
      rewrite [comp.right_inverse], exact indexed_list_rel_of_Q !idE},
    { refine rtrans (indexed_list_rel_of_Q !EDE) _,
      rewrite [comp.right_inverse, respect_id], exact indexed_list_rel_of_Q !idE},
    { refine rtrans (indexed_list_rel_of_Q !DED) _,
      rewrite [comp.right_inverse, respect_id], exact indexed_list_rel_of_Q !idD}
  end

  definition Groupoid_pushout [constructor] : Groupoid :=
  Groupoid_indexed_list (pushout_hom_rel_index F G) (pushout_index_inv F G)
    (pushout_index_reverse F G) (pushout_index_li F G) (pushout_index_ri F G)


end category
