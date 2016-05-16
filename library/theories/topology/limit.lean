/-
Copyright (c) 2016 Jacob Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Gross, Jeremy Avigad

Limits, following Hölzl, Immler, and Huffman, "Type classes and filters for mathematical analysis
in Isabelle/HOL".

The central notion in this file is

  tendsto f F₂ F₁

which says that f "tends to" filter F₂, as the input "tends to" filter F₁.  If f : X → Y, F₁ is a
filter on X, and F₂ is a filter on Y.

We can then use notation like this:

  f ⟶ y [at x]

... which is actually a composition of two notations: the first describes the function and the
target filter, and the second desribes the source filter.

We define the following filters:

  nhds x                           := neighborhoods of x
  [at x within s] := at_within x s := neighborhoods of x intersected with s \ '{x}
  [at x]          := at_elt x      := [at x within univ]
  [at x-]         := at_left x     := [at x within '(-∞, x)
  [at x+]         := at_right x    := [at x within '(x, ∞)
  [at ∞]          := at_infty      := "neighborhoods" of ∞
  [at -∞]         := at_ninfty     := "neighborhoods" of -∞

We also define the following abbreviations and notatations for modes of convergence:

  f ⟶ y   := approaches f y     := tendsto f (nhds y)
  f ⟶ ∞   := approaches_infty f := tendsto f at_infty
  f ⟶ -∞  := approaches_ninfty  := tendsto f at_ninfty

Thus, for example, "f ⟶ y [at x]" denotes "tendsto f (nhds y) (at_elt x)".

Note that lambdas are needed for functions given by expressions, for example:

  (λ x, x^2) ⟶ 4 [at 2]
  (λ x, x^2) ⟶ ∞ [at -∞]

Using the theorems can take some getting used to. "tendsto f F₂ F₁" is equivalent to

  ∀ P : Y → Prop, eventually P F₂ → eventually (λ x, P (f x)) F₁

In terms of sets, this is equivalent to

  ∀ s : set Y, s ∈ sets F₂ → f '- s ∈ sets F₁

so one option is to use "tendsto_intro" "tendsto_elim" and "tendsto_iff" to unpack meanings
in terms of "eventually", and then use the intro and elim rules of "eventually". For specific
topologies -- for example, those given by a metric space or norm -- see the specialized
intro and elim rules for eventually in those files.

For "approaches", "approaches_infty", and "approaches_ninfty", there are specific intro, elim,
and iff rules. Again, see also specific versions for metric spaces, normed spaces, etc.

Note that the filters at_infty and at_ninfty don't rely on topological notions at all, only the
existence of a suitable order.
-/
import data.set data.nat algebra.interval .basic
import theories.move   -- TODO: remove after move to Lean 3
open set function set.filter interval

namespace topology

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

-- characterize mapfilter in terms of predicates and eventually

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


/- tendsto -/

definition tendsto (f : X → Y) (F₂ : filter Y) (F₁ : filter X) : Prop := mapfilter f F₁ ≤ F₂

theorem tendsto_of_forall_eventually {F₂ : filter Y} {F₁ : filter X} {f : X → Y}
    (H : ∀ P, eventually P F₂ → eventually P (mapfilter f F₁)) :
  tendsto f F₂ F₁ := H

theorem eventually_mapfilter_of_tendsto {F₂ : filter Y} {F₁ : filter X} {f : X → Y}
    {P : Y → Prop} (H : tendsto f F₂ F₁) (H' : eventually P F₂) :
  eventually P (mapfilter f F₁) := H H'

theorem tendsto_iff (F₂ : filter Y) (F₁ : filter X) (f : X → Y) :
  tendsto f F₂ F₁ ↔ (∀ P, eventually P F₂ → eventually P (mapfilter f F₁)) :=
iff.refl _

theorem tendsto_iff' (F₂ : filter Y) (F₁ : filter X) (f : X → Y) :
  tendsto f F₂ F₁ ↔ (∀ P, eventually P F₂ → eventually (λ x, P (f x)) F₁) :=
iff.refl _

theorem tendsto_comp {f : X → Y} {g : Y → Z} {F₁ : filter X} {F₂ : filter Y} {F₃ : filter Z}
  (Hf : tendsto f F₂ F₁) (Hg : tendsto g F₃ F₂) : tendsto (g ∘ f) F₃ F₁ :=
tendsto_of_forall_eventually
  (take P, suppose eventually P F₃,
    have eventually P (mapfilter g F₂), from Hg this,
    have eventually (λ y, P (g y)) F₂, from eventually_of_eventually_mapfilter this,
    have eventually (λ y, P (g y)) (mapfilter f F₁), from Hf this,
    show eventually P (mapfilter g (mapfilter f F₁)), from eventually_mapfilter this)

theorem tendsto_of_ge {f : X → Y} {F₂ F₂' : filter Y} {F₁ : filter X}
  (HF₂ : F₂' ≥ F₂) (H : tendsto f F₂ F₁) : tendsto f F₂' F₁ :=
take P, suppose eventually P F₂',
have eventually P F₂, from eventually_of_le this HF₂,
show eventually P (mapfilter f F₁), from H this

theorem tendsto_of_le {f : X → Y} {F₂ : filter Y} {F₁ F₁' : filter X}
  (HF₁ : F₁' ≤ F₁) (H : tendsto f F₂ F₁) : tendsto f F₂ F₁' :=
take P, suppose eventually P F₂,
have eventually P (mapfilter f F₁), from H this,
show eventually P (mapfilter f F₁'), from eventually_of_le this (mapfilter_le_mapfilter _ HF₁)

theorem tendsto_of_ge_of_le {f : X → Y} {F₂ F₂' : filter Y} {F₁ F₁' : filter X}
  (HF₂ : F₂' ≥ F₂) (HF₁ : F₁' ≤ F₁) (H : tendsto f F₂ F₁) : tendsto f F₂' F₁' :=
tendsto_of_ge HF₂ (tendsto_of_le HF₁ H)

theorem tendsto_id {F : filter X} : tendsto (λx, x) F F :=
take P, assume H, H

theorem tendsto_inf_left {f : X → Y} {F : filter Y} (F₁ : filter X) {F₂ : filter X}
    (H : tendsto f F F₁) :
  tendsto f F (inf F₁ F₂) :=
tendsto_of_le !inf_le_left H

theorem tendsto_inf_right {f : X → Y} {F : filter Y} {F₁ : filter X} (F₂ : filter X)
    (H : tendsto f F F₂) :
  tendsto f F (inf F₁ F₂) :=
tendsto_of_le !inf_le_right H

theorem tendsto_sup_left {f : X → Y} (F₁ : filter Y) {F₂ : filter Y} {F : filter X}
    (H : tendsto f F₁ F) :
  tendsto f (sup F₁ F₂) F :=
tendsto_of_ge !le_sup_left H

theorem tendsto_sup_right {f : X → Y} {F₁ : filter Y} (F₂ : filter Y) {F : filter X}
    (H : tendsto f F₂ F) :
  tendsto f (sup F₁ F₂) F :=
tendsto_of_ge !le_sup_right H

theorem tendsto_comp_iff_tendsto_mapfilter (f : X → Y) (g : Y → Z) (F₁ : filter X) (F₂ : filter Z) :
  tendsto (g ∘ f) F₂ F₁ ↔ tendsto g F₂ (mapfilter f F₁) :=
!iff.refl


/- at_infty -/

section linorderX
  variable [linear_strong_order_pair X]

  definition at_infty : filter X := Inf ((λ x : X, principal '[x, ∞)) ' univ)

  notation `[at ` `∞]`  := at_infty

  private lemma principal_Ici_le_principal_Ici {x₁ x₂ : X} (H : x₁ ≤ x₂) :
    (principal '[x₂, ∞)) ≤ (principal '[x₁, ∞)) :=
  principal_le_principal (show '[x₂, ∞) ⊆ '[x₁, ∞), from λ y Hy, le.trans H Hy)

  theorem eventually_at_infty {P : X → Prop} {x : X} (H : ∀ y, y ≥ x → P y) :
    eventually P at_infty :=
  have H' : eventually P (principal '[x, ∞)), from eventually_principal H,
  have principal '[x, ∞) ∈ (λ x : X, principal '[x, ∞)) ' univ, from mem_image_of_mem _ !mem_univ,
  eventually_Inf this H'

  theorem exists_forall_ge_imp_of_eventually_at_infty {P : X → Prop} [inhabited X]
      (H : eventually P at_infty) :
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
    from exists_eventually_of_eventually_Inf this H H',
  obtain F [FS ePF], from this,
  obtain x [xuniv Feq], from FS,
  have P ⊇ '[x, ∞), from subset_of_eventually_principal (eq.subst (eq.symm Feq) ePF),
  exists.intro x this

  theorem eventually_at_infty_iff (P : X → Prop) [inhabited X] :
    eventually P at_infty ↔ ∃ x, ∀ y, y ≥ x → P y :=
  iff.intro exists_forall_ge_imp_of_eventually_at_infty
    (assume H, obtain x Hx, from H, eventually_at_infty Hx)
end linorderX


/- at_ninfty -/

section linorderX
  variable [linear_strong_order_pair X]

  definition at_ninfty : filter X := Inf ((λ x : X, principal '(-∞, x]) ' univ)

  notation `[at ` `-∞]` := at_ninfty

  private lemma principal_Iic_le_principal_Iic {x₁ x₂ : X} (H : x₁ ≤ x₂) :
    (principal '(-∞, x₁]) ≤ (principal '(-∞, x₂]) :=
  principal_le_principal (show '(-∞, x₁] ⊆ '(-∞, x₂], from λ y Hy, le.trans Hy H)

  theorem eventually_at_ninfty {P : X → Prop} {x : X} (H : ∀ y, y ≤ x → P y) :
    eventually P at_ninfty :=
  have H' : eventually P (principal '(-∞, x]), from eventually_principal H,
  have principal '(-∞, x] ∈ (λ x : X, principal '(-∞, x]) ' univ, from mem_image_of_mem _ !mem_univ,
  eventually_Inf this H'

  theorem exists_forall_le_imp_of_eventually_at_ninfty {P : X → Prop} [inhabited X]
      (H : eventually P at_ninfty) :
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
    from exists_eventually_of_eventually_Inf this H H',
  obtain F [FS ePF], from this,
  obtain x [xuniv Feq], from FS,
  have P ⊇ '(-∞, x], from subset_of_eventually_principal (eq.subst (eq.symm Feq) ePF),
  exists.intro x this

  theorem eventually_at_ninfty_iff (P : X → Prop) [inhabited X] :
    eventually P at_ninfty ↔ ∃ x, ∀ y, y ≤ x → P y :=
  iff.intro exists_forall_le_imp_of_eventually_at_ninfty
    (assume H, obtain x Hx, from H, eventually_at_ninfty Hx)
end linorderX


/- approaches_infty -/

section approaches_infty
  variable [linear_strong_order_pair Y]

  abbreviation approaches_infty (f : X → Y) := tendsto f at_infty

  notation f ` ⟶ ` ∞   := tendsto f at_infty
  notation f ` ⟶ ` -∞  := tendsto f at_ninfty

  theorem approaches_infty_intro [inhabited Y] {f : X → Y} {F : filter X}
      (H : ∀ y, eventually (λ x, f x ≥ y) F) :
    (f ⟶ ∞) F :=
  tendsto_of_forall_eventually
    (take P,
      suppose eventually P at_infty,
      obtain z (Hz : ∀ y, y ≥ z → P y), from exists_forall_ge_imp_of_eventually_at_infty this,
      have ∀ x, f x ≥ z → P (f x), from take x, Hz (f x),
      have eventually (λ x, P (f x)) F, from eventually_mono (H z) this,
      show eventually P (mapfilter f F), from eventually_mapfilter this)

  theorem approaches_infty_elim {f : X → Y} {F : filter X} (H : (f ⟶ ∞) F) (y : Y) :
    eventually (λ x, f x ≥ y) F :=
  have eventually (λ x, x ≥ y) at_infty, from eventually_at_infty (take x, suppose x ≥ y, this),
  have eventually (λ x, x ≥ y) (mapfilter f F), from H this,
  show eventually (λ x, f x ≥ y) F, from eventually_of_eventually_mapfilter this

  theorem approaches_infty_iff [inhabited Y] (f : X → Y) (F : filter X) :
    (f ⟶ ∞) F ↔ ∀ y, eventually (λ x, f x ≥ y) F :=
  iff.intro approaches_infty_elim approaches_infty_intro

  theorem approaches_infty_of_eventually_ge [inhabited Y] {f g : X → Y} {F : filter X}
      (H : eventually (λ x, f x ≥ g x) F) (H' : (g ⟶ ∞) F) :
    (f ⟶ ∞) F :=
  approaches_infty_intro (take y,
    have eventually (λ x, g x ≥ y) F, from approaches_infty_elim H' y,
    show eventually (λ x, f x ≥ y) F, from
      eventually_mpr H (eventually_mpr this (eventually_of_forall _ (take x, le.trans))))
end approaches_infty


/- approaches_ninfty -/

section approaches_ninfty
  variable [linear_strong_order_pair Y]

  abbreviation approaches_ninfty (f : X → Y) := tendsto f at_ninfty

  notation f ` ⟶ ` -∞  := tendsto f at_ninfty

  theorem approaches_ninfty_intro [inhabited Y] {f : X → Y} {F : filter X}
      (H : ∀ y, eventually (λ x, f x ≤ y) F) :
    (f ⟶ -∞) F :=
  tendsto_of_forall_eventually
    (take P,
      suppose eventually P at_ninfty,
      obtain z (Hz : ∀ y, y ≤ z → P y), from exists_forall_le_imp_of_eventually_at_ninfty this,
      have ∀ x, f x ≤ z → P (f x), from take x, Hz (f x),
      have eventually (λ x, P (f x)) F, from eventually_mono (H z) this,
      show eventually P (mapfilter f F), from eventually_mapfilter this)

  theorem approaches_ninfty_elim {f : X → Y} {F : filter X} (H : (f ⟶ -∞) F) (y : Y) :
    eventually (λ x, f x ≤ y) F :=
  have eventually (λ x, x ≤ y) at_ninfty, from eventually_at_ninfty (take x, suppose x ≤ y, this),
  have eventually (λ x, x ≤ y) (mapfilter f F), from H this,
  show eventually (λ x, f x ≤ y) F, from eventually_of_eventually_mapfilter this

  theorem approaches_ninfty_iff [inhabited Y] (f : X → Y) (F : filter X) :
    (f ⟶ -∞) F ↔ ∀ y, eventually (λ x, f x ≤ y) F :=
  iff.intro approaches_ninfty_elim approaches_ninfty_intro

  theorem approaches_ninfty_of_eventually_le [inhabited Y] {f g : X → Y} {F : filter X}
      (H : eventually (λ x, f x ≤ g x) F) (H' : (g ⟶ -∞) F) :
    (f ⟶ -∞) F :=
  approaches_ninfty_intro (take y,
    have eventually (λ x, g x ≤ y) F, from approaches_ninfty_elim H' y,
    show eventually (λ x, f x ≤ y) F, from
      eventually_mpr H (eventually_mpr this (eventually_of_forall _
        (take x H₁ H₂, le.trans H₂ H₁))))
end approaches_ninfty


/- the nhds filter -/

open topology

section nhds_filter
  variables [topology X] {P : X → Prop}

  definition nhds (x : X) : filter X := Inf (principal ' {s | Open s ∧ x ∈ s})

  proposition eventually_nhds {x : X} {s : set X} (Os : Open s) (xs : x ∈ s) (H : ∀₀ x ∈ s, P x) :
    eventually P (nhds x) :=
  eventually_Inf (mem_image_of_mem _ (and.intro Os xs)) (eventually_principal H)

  proposition eventually_mem_nhds {x : X} {s : set X} (Os : Open s) (xs : x ∈ s) :
    eventually (λ x, x ∈ s) (nhds x) :=
  eventually_nhds Os xs (λ x Hx, Hx)

  proposition exists_of_eventually_nhds {x : X} (H : eventually P (nhds x)) :
    ∃ s, Open s ∧ x ∈ s ∧ ∀₀ x ∈ s, P x :=
  let princS := principal ' {s | Open s ∧ x ∈ s} in
  have principal univ ∈ princS,
    from mem_image_of_mem principal (and.intro Open_univ !mem_univ),
  have ∃₀ F ∈ princS, eventually P F, from
    exists_eventually_of_eventually_Inf this H
     (λ F₁ (F₁mem : F₁ ∈ princS) F₂ (F₂mem : F₂ ∈ princS),
       obtain s₁ [[Os₁ xs₁] (F₁eq : principal s₁ = F₁)], from F₁mem,
       obtain s₂ [[Os₂ xs₂] (F₂eq : principal s₂ = F₂)], from F₂mem,
       have F₁ ⊓ F₂ ∈ princS,
         begin
          rewrite [-F₁eq, -F₂eq, principal_inf_principal],
          exact mem_image_of_mem _ (and.intro (Open_inter Os₁ Os₂) (mem_inter xs₁ xs₂))
         end,
       show ∃₀ F ∈ princS, F ≤ F₁ ⊓ F₂, from exists.intro _ (and.intro this !le.refl)),
  obtain F [Fmem ePF], from this,
  obtain s [[Os xs] (Feq : principal s = F)], from Fmem,
  exists.intro s (and.intro Os (and.intro xs
    (subset_of_eventually_principal (by rewrite Feq; exact ePF))))

  proposition eventually_nhds_iff (x : X) :
    eventually P (nhds x) ↔ ∃ s, Open s ∧ x ∈ s ∧ ∀₀ x ∈ s, P x :=
  iff.intro exists_of_eventually_nhds
    (assume H, obtain s [Os [xs Hs]], from H, eventually_nhds Os xs Hs)
end nhds_filter


/- the at_within filter -/

section at_within
  variables [topology X] {P : X → Prop}

  definition at_within (x : X) (s : set X) : filter X := inf (nhds x) (principal (s \ '{x}))

  notation [at x ` within ` s] := at_within x s

  proposition eventually_at_within {x : X} {s t : set X} (Os : Open s) (xs : x ∈ s)
      (Hs : ∀₀ y ∈ s, y ≠ x → y ∈ t → P y) :
    eventually P [at x within t] :=
  have H₁ : eventually (λ y, y ≠ x → y ∈ t → P y) (nhds x),
    from eventually_nhds Os xs Hs,
  eventually_inf H₁ _ (mem_principal _)
    (take y, assume Hy,
      have H : y ∈ t \ '{x}, from and.right Hy,
      have H' : y ≠ x, from suppose y = x,
        have y ∈ '{x}, from mem_singleton_of_eq this,
        show false, from and.right H this,
      show P y, from and.left Hy `y ≠ x` (and.left H))

  proposition exists_of_eventually_at_within {x : X} {t : set X}
     (H : eventually P [at x within t]) :
    ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y ≠ x → y ∈ t → P y :=
  obtain P₁ [eP₁nhds [P₂ [eP₂princ (H' : P ⊇ P₁ ∩ P₂)]]], from exists_of_eventually_inf H,
  obtain s [Os [xs Hs]], from exists_of_eventually_nhds eP₁nhds,
  have Ht : ∀₀ y ∈ t \ '{x}, P₂ y, from subset_of_eventually_principal eP₂princ,
  exists.intro s (and.intro Os (and.intro xs
    (take y, assume ys ynex yt,
      have y ∉ '{x}, from assume ymem, ynex (eq_of_mem_singleton ymem),
      show P y, from H' (and.intro (Hs y ys) (Ht (mem_diff yt this))))))

  theorem eventually_at_within_iff (x : X) {s : set X} :
    eventually P [at x within s] ↔ ∃ t, Open t ∧ x ∈ t ∧ ∀₀ y ∈ t, y ≠ x → y ∈ s → P y :=
  iff.intro exists_of_eventually_at_within
    (assume H, obtain t [Ot [xt Ht]], from H, eventually_at_within Ot xt Ht)

  abbreviation at_elt (x : X) : filter X := at_within x univ

  notation [at x] := at_elt x

  proposition eventually_at {x : X} {s : set X} (Os : Open s) (xs : x ∈ s)
      (Hs : ∀₀ y ∈ s, y ≠ x → P y) :
    eventually P [at x] :=
  eventually_at_within Os xs (take y, assume ys ynex yuniv, Hs ys ynex)

  proposition exists_of_eventually_at {x : X} (H : eventually P [at x]) :
    ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y ≠ x → P y :=
  obtain s [Os [xs Hs]], from exists_of_eventually_at_within H,
  exists.intro s (and.intro Os (and.intro xs (λ y ys ynex, Hs y ys ynex trivial)))

  proposition eventually_at_iff (x : X) :
    eventually P [at x] ↔ ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y ≠ x → P y :=
  iff.intro exists_of_eventually_at
    (assume H, obtain s [Os [xs Hs]], from H, eventually_at Os xs Hs)

  proposition at_within_eq_of_Open {x : X} {s : set X} (Os : Open s) (xs : x ∈ s) :
    [at x within s] = [at x] :=
  filter.eq (ext (take P, iff.intro
    (assume H,
      obtain t [Ot [xt Ht]], from exists_of_eventually_at_within H,
      eventually_at (Open_inter Os Ot) (mem_inter xs xt)
        (λ y Hy yne, Ht _ (and.right Hy) yne (and.left Hy)))
    (assume H,
      obtain t [Ot [xt Ht]], from exists_of_eventually_at H,
      eventually_at_within (Open_inter Os Ot) (mem_inter xs xt)
        (λ y Hy yne ys, Ht _ (and.right Hy) yne))))
end at_within


/- at_left and at_right -/

section at_left_at_right
  variables [topology X] [linear_strong_order_pair X] {P : X → Prop}

  abbreviation at_left (x : X) : filter X := [at x within '(-∞, x)]
  abbreviation at_right (x : X) : filter X := [at x within '(x, ∞)]

  notation [at x`-]` := at_left x
  notation [at x`+]` := at_right x

  proposition eventually_at_left {x : X} {s : set X} (Os : Open s) (xs : x ∈ s)
      (H : ∀₀ y ∈ s, y < x → P y) :
    eventually P [at x-] :=
  eventually_at_within Os xs (take y, assume ys ynex yltx, H ys yltx)

  proposition exists_of_eventually_at_left {x : X} (H : eventually P [at x-]) :
    ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y < x → P y :=
  obtain s [Os [xs Hs]], from exists_of_eventually_at_within H,
  exists.intro s (and.intro Os (and.intro xs
    (take y, assume ys yltx,
      show P y, from Hs y ys (ne_of_lt yltx) yltx)))

  variable (P)
  proposition eventually_at_left_iff (x : X) :
    eventually P [at x-] ↔ ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y < x → P y :=
  iff.intro exists_of_eventually_at_left
    (take H, obtain s [Os [xs Hs]], from H, eventually_at_left Os xs Hs)

  variable {P}
  proposition eventually_at_right {x : X} {s : set X} (Os : Open s) (xs : x ∈ s)
      (H : ∀₀ y ∈ s, y > x → P y) :
    eventually P [at x+] :=
  eventually_at_within Os xs (take y, assume ys ynex yltx, H ys yltx)

  proposition exists_of_eventually_at_right {x : X} (H : eventually P [at x+]) :
    ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y > x → P y :=
  obtain s [Os [xs Hs]], from exists_of_eventually_at_within H,
  exists.intro s (and.intro Os (and.intro xs
    (take y, assume ys yltx,
      show P y, from Hs y ys (ne_of_gt yltx) yltx)))

  variable (P)
  proposition eventually_at_right_iff (x : X) :
    eventually P [at x+] ↔ ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y > x → P y :=
  iff.intro exists_of_eventually_at_right
    (take H, obtain s [Os [xs Hs]], from H, eventually_at_right Os xs Hs)
end at_left_at_right


/- approaches -/

section approaches
  variables [topology Y]
  variables {F : filter X} {f : X → Y} {y : Y}

  abbreviation approaches (f : X → Y) (y : Y) : filter X → Prop := tendsto f (nhds y)

  notation f ⟶ y := approaches f y

  proposition approaches_intro (H : ∀ s, Open s → y ∈ s → eventually (λ x, f x ∈ s) F) :
    (f ⟶ y) F :=
  tendsto_of_forall_eventually
    (take P, assume eventuallyP,
      obtain s [Os [(ys : y ∈ s) (H' : ∀₀ y' ∈ s, P y')]],
        from exists_of_eventually_nhds eventuallyP,
      have eventually (λ x, P (f x)) F, from eventually_mono (H s Os ys) (λ x Hx, H' Hx),
      show eventually P (mapfilter f F), from eventually_mapfilter this)

  proposition approaches_elim (H : (f ⟶ y) F) {s : set Y} (Os : Open s) (ys : y ∈ s) :
    eventually (λ x, f x ∈ s) F :=
  have eventually (λ y', y' ∈ s) (mapfilter f F),
    from eventually_mapfilter_of_tendsto H (eventually_mem_nhds Os ys),
  eventually_of_eventually_mapfilter this

  variables (F f y)
  proposition approaches_iff : (f ⟶ y) F ↔ (∀ s, Open s → y ∈ s → eventually (λ x, f x ∈ s) F) :=
  iff.intro approaches_elim approaches_intro
end approaches

end topology
