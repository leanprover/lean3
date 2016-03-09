/-
Copyright (c) 2016 Jacob Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Gross, Jeremy Avigad

Limits, following Hölzl, Immler, and Huffman, "Type classes and filters for mathematical
analysis in Isabelle/HOL".

We are experimenting with notation like this:

  f ⟶ y [at x]

... which is actually a composition of two notations: the first describes the function and
the target filter, and the second desribes the source filter.

Variations on the first can include:

  f ⟶ ∞
  f ⟶ -∞
  f ⟶+ y          convergence from the right
  f ⟶- y          convergence from the left
  f ⟶ y within s  convergences within a set

Variations on the second can include:

  [at ∞]
  [at -∞]
  [at x]
  [at+ x]
  [at- x]
  [at x within s]

When written consecutively, we get filterlim f F₂ F₁, where the first notation gives f and F₂,
and the second gives F₁.

Note that lambdas are needed for functions given by expressions:

  (λ x, x^2) ⟶ 4 [at 2]
  (λ x, x^2) ⟶ ∞ [at -∞]

If making `[at` a token is problematic, we can add a tick mark or something.
-/
import data.set data.nat algebra.order algebra.interval
open set function set.filter interval


-- TODO: move to data/set/basic

theorem singleton_subset {X : Type} {a : X} {s : set X} (H : a ∈ s) : '{a} ⊆ s :=
take b, suppose b ∈ '{a},
have b = a, from eq_of_mem_singleton this,
show b ∈ s, by rewrite this; assumption

theorem mem_of_singleton_subset {X : Type} {a : X} {s : set X} (H : '{a} ⊆ s) : a ∈ s :=
H (mem_singleton a)

theorem singleton_subset_iff {X : Type} (a : X) (s : set X) : '{a} ⊆ s ↔ a ∈ s :=
iff.intro mem_of_singleton_subset singleton_subset

-- TODO: move these to data/set/filter

namespace filter
  protected theorem le_iff {X : Type} (F₁ F₂ : filter X) : F₁ ≤ F₂ ↔ F₂ ⊆ F₁ := iff.refl _
end filter

-- TODO: change names of fields in filter
-- TODO: reorder hypotheses in eventually_of_le, and change "le" to "ge"
-- TODO: fix eventually_inf: implicit argument, and use implication
-- TODO: set: add spaces around ∀₀ x ∈ s and ∃₀ x ∈ s

theorem eventually_inf_left {X : Type} {P : X → Prop} {F₁ : filter X} (F₂ : filter X)
  (H : eventually P F₁) : eventually P (inf F₁ F₂) :=
eventually_of_le H !inf_le_left

theorem eventually_inf_right {X : Type} {P : X → Prop} (F₁ : filter X) {F₂ : filter X}
  (H : eventually P F₂) : eventually P (inf F₁ F₂) :=
eventually_of_le H !inf_le_right

theorem eventually_Inf {X : Type} {P : X → Prop} {S : set (filter X)} {F : filter X} (FS : F ∈ S)
  (H : eventually P F) : eventually P (Inf S) :=
eventually_of_le H (Inf_le FS)

-- TODO: replace definition of Inf with this

definition Inf' {X : Type} (S : set (filter X)) : filter X :=
⦃ filter,
  sets          := { s | ∃ T : set (set X), finite T ∧ T ⊆ (⋃ F ∈ S, sets F) ∧ ⋂₀ T ⊆ s},
  univ_mem_sets :=  abstract
                      have H : (⋂₀ ∅) ⊆ @univ X, by rewrite sInter_empty; apply subset.refl,
                      exists.intro ∅ (and.intro !finite_empty (and.intro (empty_subset _) H))
                    end,
  inter_closed  := abstract
                     take s t, assume Hs Ht,
                     obtain Ts finTs Tssub ITs, from Hs,
                     obtain Tt finTt Ttsub ITt, from Ht,
                     have H1 : finite (Ts ∪ Tt), proof finite_union Ts Tt qed,
                     have H2 : Ts ∪ Tt ⊆ (⋃ F ∈ S, sets F), from union_subset Tssub Ttsub,
                     have H3 : ⋂₀ (Ts ∪ Tt) ⊆ s ∩ t,
                     begin
                       rewrite sInter_union, apply subset_inter,
                         {exact subset.trans (inter_subset_left _ _) ITs},
                       exact subset.trans (inter_subset_right _ _) ITt
                     end,
                     exists.intro _ (and.intro H1 (and.intro H2 H3))
                   end,
  is_mono       := abstract
                     take s t ssubt Hs,
                     obtain T finT Tsub IT, from Hs,
                     exists.intro T (and.intro finT (and.intro Tsub (subset.trans IT ssubt)))
                   end
⦄

theorem sets_Inf' {A : Type} (S : set (filter A)) :
  sets (Inf' S) = { s | ∃ T : set (set A), finite T ∧ T ⊆ (⋃ F ∈ S, sets F) ∧ ⋂₀ T ⊆ s} :=
rfl

theorem sInter_mem_of_finite {A : Type} {F : filter A} {T : set (set A)} (finT : finite T)
    (Tsub : T ⊆ sets F) : ⋂₀ T ∈ sets F :=
begin
  induction finT with a T finT aninT ih,
    {rewrite sInter_empty, apply filter.univ_mem_sets},
  rewrite sInter_insert, apply filter.inter_closed,
    show a ∈ sets F, from Tsub (mem_insert a T),
  show ⋂₀ T ∈ sets F, from ih (subset.trans (subset_insert _ _) Tsub)
end

theorem le_Inf' {A : Type} {F : filter A} {S : set (filter A)} (H : ∀₀ G ∈ S, F ≤ G) :
  F ≤ Inf' S :=
filter.le_of_subset
  (take s, suppose s ∈ sets (Inf' S),
    obtain (T : set (set A)) finT (Tsub : T ⊆ (⋃ G ∈ S, sets G)) (IT : ⋂₀ T ⊆ s), from this,
    have T ⊆ sets F, from subset.trans Tsub (bUnion_subset H),
    have ⋂₀ T ∈ sets F, from sInter_mem_of_finite finT this,
    show s ∈ sets F, from filter.is_mono _ IT this)

theorem Inf'_le {A : Type} {F : filter A} {S : set (filter A)} (FS : F ∈ S) :
  Inf' S ≤ F :=
filter.le_of_subset
  (take s, suppose s ∈ sets F,
    have '{s} ⊆ ⋃ G ∈ S, sets G, from singleton_subset (mem_bUnion FS this),
    exists.intro '{s} (and.intro _
      (and.intro this (by rewrite sInter_singleton; apply subset.refl))))

theorem Inf_eq_Inf' {A : Type} (S : set (filter A)) : Inf S = Inf' S :=
le.antisymm (le_Inf' (λ F FS, Inf_le FS)) (le_Inf (λ F FS, Inf'_le FS))

theorem exists_eventually_of_eventually_Inf {A : Type} {P : A → Prop} {F : filter A}
    {S : set (filter A)} (FS : F ∈ S) (H : ∀₀ F₁ ∈ S, ∀₀ F₂ ∈ S, ∃₀ F ∈ S, F ≤ inf F₁ F₂)
    (H' : eventually P (Inf S)) :
  ∃₀ F ∈ S, eventually P F :=
have P ∈ Inf' S, by rewrite -Inf_eq_Inf'; apply H',
have ∃ T : set (set A), finite T ∧ T ⊆ (⋃ F ∈ S, sets F) ∧ ⋂₀ T ⊆ P,
  by rewrite sets_Inf' at this; exact this,
obtain T finT Tsub ITP, from this,
have ∃₀ F ∈ S, ⋂₀ T ∈ F,
  begin
    clear ITP,
    induction finT with s T finT sninT ih,
      {exact exists.intro F (and.intro FS (by rewrite sInter_empty; apply filter.univ_mem_sets))},
    have ∃₀ F ∈ S, ⋂₀ T ∈ F, from ih (subset.trans (subset_insert _ _) Tsub),
    cases this with F₁ H₁,
    cases H₁ with F₁S ITF₁,
    have s ∈ (⋃ F ∈ S, sets F), from Tsub !mem_insert,
    cases this with F₂ H₂,
    cases H₂ with F₂S sF₂,
    cases H F₁S F₂S with F' HF',
    cases HF' with F'S F'le,
    existsi F', split, exact F'S,
    show ⋂₀ insert s T ∈ sets F',
      begin
        rewrite sInter_insert, apply filter.inter_closed,
          show s ∈ sets F', from filter.subset_of_le (le.trans F'le !inf_le_right) sF₂,
        show ⋂₀ T ∈ sets F', from filter.subset_of_le (le.trans F'le !inf_le_left) ITF₁,
      end
  end,
obtain F FS IT, from this,
exists.intro F (and.intro FS (filter.is_mono _ ITP IT))


-- the file proper starts here

variables {X Y Z : Type}

/- mapfilter -/

section
  local attribute mem [reducible]

  definition mapfilter (f : X → Y) (F : filter X) : filter Y :=
  ⦃ filter,
    sets          := λ s, (f '- s) ∈ F,
    univ_mem_sets := abstract !univ_mem_sets end,
    inter_closed  := abstract take a b, assume Ha Hb, !inter_closed Ha Hb end,
    is_mono       := abstract take a b, assume Hab Ha, !is_mono (λ x H, Hab (f x) H) Ha end
  ⦄
end

-- characterize mapfilter in terms of set membership

theorem mem_mapfilter_iff (s : set Y) (F : filter X) (f : X → Y) :
  s ∈  mapfilter f F ↔ (f '- s) ∈ F :=
!iff.refl

theorem mem_mapfilter {s : set Y} {F : filter X} {f : X → Y} (H : f '- s ∈ F) :
  s ∈ mapfilter f F := H

theorem preimage_mem_filter_of_mem_mapfilter {s : set Y} {F : filter X} {f : X → Y}
    (H : s ∈ mapfilter f F) :
  f '- s ∈ F := H

-- characterize mapfilter in terms of eventually and predicates

theorem eventually_mapfilter_iff (P : Y → Prop) (F : filter X) (f : X → Y) :
  eventually P (mapfilter f F) ↔ eventually (λ x, P (f x)) F :=
!iff.refl

theorem eventually_mapfilter {P : Y → Prop} {F : filter X} {f : X → Y}
    (H : eventually (λ x, P (f x)) F) :
  eventually P (mapfilter f F) := H

theorem eventually_of_eventually_mapfilter {P : Y → Prop} {F : filter X} {f : X → Y}
    (H : eventually P (mapfilter f F)) :
  eventually (λ x, P (f x)) F:= H

-- other properties

theorem mapfilter_id (F : filter Y) : mapfilter (λ x, x) F = F := filter.eq rfl

theorem mapfilter_comp (F : filter X) (g : Y → Z) (f : X → Y) :
  mapfilter (g ∘ f) F = mapfilter g (mapfilter f F) := rfl

theorem mapfilter_le_mapfilter {F F' : filter X} (f : X → Y) (H : F ≤ F') :
  mapfilter f F ≤ mapfilter f F' :=
begin
  rewrite filter.le_iff, intro s, rewrite *mem_mapfilter_iff,
  apply filter.subset_of_le H
end
-- alternative proof: take s, assume H', by unfold mem; exact H H'

theorem mapfilter_bot (f : X → Y) : mapfilter f ⊥ = ⊥ :=
filter.eq (by rewrite *filter.bot_eq)

theorem mapfilter_sup (f : X → Y) (F F' : filter X) :
  mapfilter f (sup F F') = sup (mapfilter f F) (mapfilter f F') :=
filter.eq (ext (take x, !iff.refl))

theorem mapfilter_inf (f : X → Y) (F F' : filter X) :
  mapfilter f (inf F F') ≤ inf (mapfilter f F) (mapfilter f F') :=
le_inf (mapfilter_le_mapfilter f !inf_le_left) (mapfilter_le_mapfilter f !inf_le_right)


/- limits -/

definition filterlim (f : X → Y) (F₂ : filter Y) (F₁ : filter X) : Prop := mapfilter f F₁ ≤ F₂

theorem filterlim_of_forall_eventually {F₂ : filter Y} {F₁ : filter X} {f : X → Y}
    (H : ∀ P, eventually P F₂ → eventually P (mapfilter f F₁)) :
  filterlim f F₂ F₁ := H

theorem eventually_mapfilter_of_filterlim {F₂ : filter Y} {F₁ : filter X} {f : X → Y}
    {P : Y → Prop} (H : filterlim f F₂ F₁) (H' : eventually P F₂) :
  eventually P (mapfilter f F₁) := H H'

theorem filterlim_iff (F₂ : filter Y) (F₁ : filter X) (f : X → Y) :
  filterlim f F₂ F₁ ↔ (∀ P, eventually P F₂ → eventually P (mapfilter f F₁)) :=
iff.refl _

theorem filterlim_iff' (F₂ : filter Y) (F₁ : filter X) (f : X → Y) :
  filterlim f F₂ F₁ ↔ (∀ P, eventually P F₂ → eventually (λ x, P (f x)) F₁) :=
iff.refl _

theorem filterlim_comp {f : X → Y} {g : Y → Z} {F₂ : filter Y} {F₁ : filter X} {F₃ : filter Z}
  (Hf : filterlim f F₂ F₁) (Hg : filterlim g F₃ F₂) : filterlim (g ∘ f) F₃ F₁ :=
filterlim_of_forall_eventually
  (take P, suppose eventually P F₃,
    have eventually P (mapfilter g F₂), from Hg this,
    have eventually (λ y, P (g y)) F₂, from eventually_of_eventually_mapfilter this,
    have eventually (λ y, P (g y)) (mapfilter f F₁), from Hf this,
    show eventually P (mapfilter g (mapfilter f F₁)), from eventually_mapfilter this)

theorem filterlim_of_ge {f : X → Y} {F₂ F₂' : filter Y} {F₁ : filter X}
  (HF₂ : F₂' ≥ F₂) (H : filterlim f F₂ F₁) : filterlim f F₂' F₁ :=
take P, suppose eventually P F₂',
have eventually P F₂, from eventually_of_le this HF₂,
show eventually P (mapfilter f F₁), from H this

theorem filterlim_of_le {f : X → Y} {F₂ : filter Y} {F₁ F₁' : filter X}
  (HF₁ : F₁' ≤ F₁) (H : filterlim f F₂ F₁) : filterlim f F₂ F₁' :=
take P, suppose eventually P F₂,
have eventually P (mapfilter f F₁), from H this,
show eventually P (mapfilter f F₁'), from eventually_of_le this (mapfilter_le_mapfilter _ HF₁)

theorem filterlim_of_ge_of_le {f : X → Y} {F₂ F₂' : filter Y} {F₁ F₁' : filter X}
  (HF₂ : F₂' ≥ F₂) (HF₁ : F₁' ≤ F₁) (H : filterlim f F₂ F₁) : filterlim f F₂' F₁' :=
filterlim_of_ge HF₂ (filterlim_of_le HF₁ H)

theorem filterlim_id {F : filter X} : filterlim (λx, x) F F :=
take P, assume H, H

theorem filterlim_inf_left {f : X → Y} {F : filter Y} (F₁ : filter X) {F₂ : filter X}
    (H : filterlim f F F₁) :
  filterlim f F (inf F₁ F₂) :=
filterlim_of_le !inf_le_left H

theorem filterlim_inf_right {f : X → Y} {F : filter Y} {F₁ : filter X} (F₂ : filter X)
    (H : filterlim f F F₂) :
  filterlim f F (inf F₁ F₂) :=
filterlim_of_le !inf_le_right H

theorem filterlim_sup_left {f : X → Y} (F₁ : filter Y) {F₂ : filter Y} {F : filter X}
    (H : filterlim f F₁ F) :
  filterlim f (sup F₁ F₂) F :=
filterlim_of_ge !le_sup_left H

theorem filterlim_sup_right {f : X → Y} {F₁ : filter Y} (F₂ : filter Y) {F : filter X}
    (H : filterlim f F₂ F) :
  filterlim f (sup F₁ F₂) F :=
filterlim_of_ge !le_sup_right H

theorem filterlim_comp_iff_filterlim_mapfilter (f : X → Y) (g : Y → Z)
    (F₁ : filter X) (F₃ : filter Z) :
  filterlim (g ∘ f) F₃ F₁ ↔ filterlim g F₃ (mapfilter f F₁) :=
!iff.refl

/- limits on orders -/

section linorderX
  variable [linear_strong_order_pair X]

  /- at_top filter, for limits as x goes to infinity -/

  definition at_top : filter X := Inf ((λ x : X, principal '[x, ∞)) ' univ)

  private lemma principal_Ici_le_principal_Ici {x₁ x₂ : X} (H : x₁ ≤ x₂) :
    (principal '[x₂, ∞)) ≤ (principal '[x₁, ∞)) :=
  principal_le_principal (show '[x₂, ∞) ⊆ '[x₁, ∞), from λ y Hy, le.trans H Hy)

  theorem eventually_at_top {P : X → Prop} {x : X} (H : ∀ y, y ≥ x → P y) : eventually P at_top :=
  have H' : eventually P (principal '[x, ∞)), from eventually_principal H,
  have principal '[x, ∞) ∈ (λ x : X, principal '[x, ∞)) ' univ, from mem_image_of_mem _ !mem_univ,
  eventually_Inf this H'

  theorem exists_forall_ge_imp_of_eventually_at_top {P : X → Prop} [inhabited X]
      (H : eventually P at_top) :
    ∃ x, ∀ y, y ≥ x → P y :=
  let S := (λ x : X, principal '[x, ∞)) ' univ in
  have H' : ∀₀ F₁ ∈ S, ∀₀ F₂ ∈ S, ∃₀ F ∈ S, F ≤ F₁ ⊓ F₂,
    proof
      take F₁, suppose F₁ ∈ S, take F₂, suppose F₂ ∈ S,
      obtain x₁ [x₁univ F₁eq], from `F₁ ∈ S`,
      obtain x₂ [x₂univ F₂eq], from `F₂ ∈ S`,
      or.elim (le_or_gt x₁ x₂)
        (suppose x₁ ≤ x₂,
          have F₂ ≤ F₁, by rewrite [-F₁eq, -F₂eq]; exact principal_Ici_le_principal_Ici this,
          exists.intro F₂ (and.intro `F₂ ∈ S` (le_inf this !le.refl)))
        (suppose x₂ < x₁,
          have x₂ ≤ x₁, from le_of_lt this,
          have F₁ ≤ F₂, by rewrite [-F₁eq, -F₂eq]; exact principal_Ici_le_principal_Ici this,
          exists.intro F₁ (and.intro `F₁ ∈ S` (le_inf !le.refl this)))
    qed,
  have principal '[arbitrary X, ∞) ∈ S,
    from mem_image_of_mem _ !mem_univ,
  have ∃₀ F ∈ S, eventually P F,
    from exists_eventually_of_eventually_Inf this H' H,
  obtain F [FS ePF], from this,
  obtain x [xuniv Feq], from FS,
  have P ⊇ '[x, ∞), from subset_of_eventually_principal (eq.subst (eq.symm Feq) ePF),
  exists.intro x this

  theorem eventually_at_top_iff (P : X → Prop) [inhabited X] :
    eventually P at_top ↔ ∃ x, ∀ y, y ≥ x → P y :=
  iff.intro exists_forall_ge_imp_of_eventually_at_top
    (assume H, obtain x Hx, from H, eventually_at_top Hx)

  /- at_bot filter, for limits as x goes to negative infinity -/

  definition at_bot : filter X := Inf ((λ x : X, principal '(-∞, x]) ' univ)

  private lemma principal_Iic_le_principal_Iic {x₁ x₂ : X} (H : x₁ ≤ x₂) :
    (principal '(-∞, x₁]) ≤ (principal '(-∞, x₂]) :=
  principal_le_principal (show '(-∞, x₁] ⊆ '(-∞, x₂], from λ y Hy, le.trans Hy H)

  theorem eventually_at_bot {P : X → Prop} {x : X} (H : ∀ y, y ≤ x → P y) : eventually P at_bot :=
  have H' : eventually P (principal '(-∞, x]), from eventually_principal H,
  have principal '(-∞, x] ∈ (λ x : X, principal '(-∞, x]) ' univ, from mem_image_of_mem _ !mem_univ,
  eventually_Inf this H'

  theorem exists_forall_le_imp_of_eventually_at_bot {P : X → Prop} [inhabited X]
      (H : eventually P at_bot) :
    ∃ x, ∀ y, y ≤ x → P y :=
  let S := (λ x : X, principal '(-∞, x]) ' univ in
  have H' : ∀₀ F₁ ∈ S, ∀₀ F₂ ∈ S, ∃₀ F ∈ S, F ≤ F₁ ⊓ F₂,
    proof
      take F₁, suppose F₁ ∈ S, take F₂, suppose F₂ ∈ S,
      obtain x₁ [x₁univ F₁eq], from `F₁ ∈ S`,
      obtain x₂ [x₂univ F₂eq], from `F₂ ∈ S`,
      or.elim (le_or_gt x₁ x₂)
        (suppose x₁ ≤ x₂,
          have F₁ ≤ F₂, by rewrite [-F₁eq, -F₂eq]; exact principal_Iic_le_principal_Iic this,
          exists.intro F₁ (and.intro `F₁ ∈ S` (le_inf !le.refl this)))
        (suppose x₂ < x₁,
          have x₂ ≤ x₁, from le_of_lt this,
          have F₂ ≤ F₁, by rewrite [-F₁eq, -F₂eq]; exact principal_Iic_le_principal_Iic this,
          exists.intro F₂ (and.intro `F₂ ∈ S` (le_inf this !le.refl)))
    qed,
  have principal '(-∞, arbitrary X] ∈ S,
    from mem_image_of_mem _ !mem_univ,
  have ∃₀ F ∈ S, eventually P F,
    from exists_eventually_of_eventually_Inf this H' H,
  obtain F [FS ePF], from this,
  obtain x [xuniv Feq], from FS,
  have P ⊇ '(-∞, x], from subset_of_eventually_principal (eq.subst (eq.symm Feq) ePF),
  exists.intro x this

  theorem eventually_at_bot_iff (P : X → Prop) [inhabited X] :
    eventually P at_bot ↔ ∃ x, ∀ y, y ≤ x → P y :=
  iff.intro exists_forall_le_imp_of_eventually_at_bot
    (assume H, obtain x Hx, from H, eventually_at_bot Hx)

  /- notation -/

  notation f ` ⟶ ` ∞   := filterlim f at_top
  notation f ` ⟶ ` -∞  := filterlim f at_bot
  notation `[at ` `∞]`  := at_top
  notation `[at ` `-∞]` := at_bot

  section examples
    variable [linear_strong_order_pair Y]
    variable f : X → Y

    -- check f ⟶ ∞ [at ∞]
    -- check f ⟶ ∞ [at -∞]
    -- check f ⟶ -∞ [at -∞]
    -- check (λ x : X, x) ⟶ ∞ [at ∞]
  end examples

end linorderX

/- limits at top and at bot -/

section linorderY

  variable [linear_strong_order_pair Y]

  theorem filterlim_at_top [inhabited Y] {f : X → Y} {F : filter X}
      (H : ∀ y, eventually (λ x, f x ≥ y) F) :
    (f ⟶ ∞) F :=
  filterlim_of_forall_eventually
    (take P,
      suppose eventually P at_top,
      obtain z (Hz : ∀ y, y ≥ z → P y), from exists_forall_ge_imp_of_eventually_at_top this,
      have ∀ x, f x ≥ z → P (f x), from take x, Hz (f x),
      have eventually (λ x, P (f x)) F, from eventually_mono (H z) this,
      show eventually P (mapfilter f F), from eventually_mapfilter this)

  theorem eventually_ge_of_filterlim_at_top {f : X → Y} {F : filter X} (H : (f ⟶ ∞) F) (y : Y) :
    eventually (λ x, f x ≥ y) F :=
  have eventually (λ x, x ≥ y) at_top, from eventually_at_top (take x, suppose x ≥ y, this),
  have eventually (λ x, x ≥ y) (mapfilter f F), from H this,
  show eventually (λ x, f x ≥ y) F, from eventually_of_eventually_mapfilter this

  theorem filterlim_at_top_iff [inhabited Y] (f : X → Y) (F : filter X) :
    (f ⟶ ∞) F ↔ ∀ y, eventually (λ x, f x ≥ y) F :=
  iff.intro eventually_ge_of_filterlim_at_top filterlim_at_top

  theorem filterlim_at_top_of_eventually_ge [inhabited Y] {f g : X → Y} {F : filter X}
      (H : eventually (λ x, f x ≥ g x) F) (H' : (g ⟶ ∞) F) :
    (f ⟶ ∞) F :=
  filterlim_at_top (take y,
    have eventually (λ x, g x ≥ y) F, from eventually_ge_of_filterlim_at_top H' y,
    show eventually (λ x, f x ≥ y) F, from
      eventually_mpr H (eventually_mpr this (eventually_of_forall _ (take x, le.trans))))

  theorem filterlim_at_bot [inhabited Y] {f : X → Y} {F : filter X}
      (H : ∀ y, eventually (λ x, f x ≤ y) F) :
    (f ⟶ -∞) F :=
  filterlim_of_forall_eventually
    (take P,
      suppose eventually P at_bot,
      obtain z (Hz : ∀ y, y ≤ z → P y), from exists_forall_le_imp_of_eventually_at_bot this,
      have ∀ x, f x ≤ z → P (f x), from take x, Hz (f x),
      have eventually (λ x, P (f x)) F, from eventually_mono (H z) this,
      show eventually P (mapfilter f F), from eventually_mapfilter this)

  theorem eventually_ge_of_filterlim_at_bot {f : X → Y} {F : filter X} (H : (f ⟶ -∞) F) (y : Y) :
    eventually (λ x, f x ≤ y) F :=
  have eventually (λ x, x ≤ y) at_bot, from eventually_at_bot (take x, suppose x ≤ y, this),
  have eventually (λ x, x ≤ y) (mapfilter f F), from H this,
  show eventually (λ x, f x ≤ y) F, from eventually_of_eventually_mapfilter this

  theorem filterlim_at_bot_iff [inhabited Y] (f : X → Y) (F : filter X) :
    (f ⟶ -∞) F ↔ ∀ y, eventually (λ x, f x ≤ y) F :=
  iff.intro eventually_ge_of_filterlim_at_bot filterlim_at_bot

  theorem filterlim_at_bot_of_eventually_ge [inhabited Y] {f g : X → Y} {F : filter X}
      (H : eventually (λ x, f x ≤ g x) F) (H' : (g ⟶ -∞) F) :
    (f ⟶ -∞) F :=
  filterlim_at_bot (take y,
    have eventually (λ x, g x ≤ y) F, from eventually_ge_of_filterlim_at_bot H' y,
    show eventually (λ x, f x ≤ y) F, from
      eventually_mpr H (eventually_mpr this (eventually_of_forall _
        (take x H₁ H₂, le.trans H₂ H₁))))
end linorderY
