-- category

import logic.core.eq logic.core.connectives
import data.unit data.sigma data.prod
import struc.function

inductive category (ob : Type) (mor : ob → ob → Type) : Type :=
cat_mk : Π (comp : Π⦃A B C : ob⦄, mor B C → mor A B → mor A C)
           (id : Π {A : ob}, mor A A),
            (Π {A B C D : ob} {f : mor A B} {g : mor B C} {h : mor C D},
            comp h (comp g f) = comp (comp h g) f) →
           (Π {A B : ob} {f : mor A B}, comp f id = f) →
           (Π {A B : ob} {f : mor A B}, comp id f = f) →
            category ob mor

namespace category

section

parameters {ob : Type} {mor : ob → ob → Type} {Cat : category ob mor}


abbreviation compose := category_rec (λ comp id assoc idr idl, comp) Cat

precedence `∘`:60
infixr  ∘ := compose

abbreviation id := category_rec (λ comp id assoc idr idl, id) Cat
abbreviation ID (A : ob) := @id A

theorem assoc : Π {A B C D : ob} {f : mor A B} {g : mor B C} {h : mor C D},
            h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
category_rec (λ comp id assoc idr idl, assoc) Cat
theorem id_right : Π {A B : ob} {f : mor A B}, f ∘ id = f :=
category_rec (λ comp id assoc idr idl, idr) Cat
theorem id_left  : Π {A B : ob} {f : mor A B}, id ∘ f = f :=
category_rec (λ comp id assoc idr idl, idl) Cat

theorem left_id_unique {A : ob} (i : mor A A) (H : Π{B} {f : mor B A}, i ∘ f = f) : i = id :=
calc
  i = i ∘ id : symm id_right
  ... = id : H

theorem right_id_unique {A : ob} (i : mor A A) (H : Π{B} {f : mor A B}, f ∘ i = f) : i = id :=
calc
  i = id ∘ i : symm id_left
  ... = id : H

definition iso {A B : ob} (f : mor A B) : Type := Σ g, f ∘ g = id ∧ g ∘ f = id
definition inverse {A B : ob} (f : mor A B) (H : iso f) : mor B A := sigma.dpr1 H

postfix `⁻¹` := inverse

theorem compose_inverse {A B : ob} {f : mor A B} (H : iso f) : f ∘ f⁻¹ H = id :=
and_elim_left (sigma.dpr2 H)

theorem inverse_compose {A B : ob} {f : mor A B} (H : iso f) : f⁻¹ H ∘ f = id :=
and_elim_right (sigma.dpr2 H)

theorem inverse_unique {A B : ob} {f : mor A B} (H H' : iso f) : f⁻¹ H = f⁻¹ H' :=
calc
  f⁻¹ H = f⁻¹ H ∘ id : symm id_right
    ... = f⁻¹ H ∘ f ∘ f⁻¹ H' : {symm (compose_inverse H')}
    ... = (f⁻¹ H ∘ f) ∘ f⁻¹ H' : assoc
    ... = id ∘ f⁻¹ H' : {inverse_compose H}
    ... = f⁻¹ H' : id_left

definition mono {A B : ob} (f : mor A B) : Prop := ∀⦃C⦄ {g h : mor C A}, f ∘ g = f ∘ h → g = h
definition epi  {A B : ob} (f : mor A B) : Prop := ∀⦃C⦄ {g h : mor B C}, g ∘ f = h ∘ f → g = h

end


using unit

definition one [instance] : category unit (λa b, unit) :=
cat_mk (λ a b c f g, star) (λ a, star) (λ a b c d f g h, unit_eq _ _)
  (λ a b f, unit_eq _ _) (λ a b f, unit_eq _ _)

check compose star star

section

parameters {obC obD : Type} {morC : obC → obC → Type} {morD : obD → obD → Type}
 (C : category obC morC)
parameter ( D : category obD morD )

instance C

-- check @id
-- check C
-- check id2

-- inductive functor :=
-- functor_mk : Π (obF : obC → obD) (morF : Π{A B}, morC A B → morD (obF A) (obF B)),
--             (Π {A : obC}, morF (id2 A) = id2 (obF A)) →
-- --            (Π {A B C : obC} {f : morC A B} {g : morC B C}, morF (g ∘ f) = morF g ∘ morF f) →
--             functor

end

-- check @functor_mk
-- check @functor_rec

section
--need extensionality
definition type_cat : category Type (λA B, A → B) :=
cat_mk (λ a b c f g, function.compose f g) (λ a, function.id) (λ a b c d f g h, sorry)
  (λ a b f, sorry) (λ a b f, sorry)

end


end category
