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

so one option is to use "tendsto_intro" "tendsto_dest" and "tendsto_iff" to unpack meanings
in terms of "eventually", and then use the intro and dest rules of "eventually". For specific
topologies -- for example, those given by a metric space or norm -- see the specialized
intro and dest rules for eventually in those files.

For "approaches", "approaches_infty", and "approaches_ninfty", there are specific intro, dest,
and iff rules. Again, see also specific versions for metric spaces, normed spaces, etc.

Note that the filters at_infty and at_ninfty don't rely on topological notions at all, only the
existence of a suitable order.

We mark tendsto as irreducible after defining the intro and dest rules, because otherwise
tactics seem to unfold too much.
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

theorem tendsto_intro' {F₂ : filter Y} {F₁ : filter X} {f : X → Y}
    (H : ∀ P, eventually P F₂ → eventually P (mapfilter f F₁)) :
  tendsto f F₂ F₁ := H

theorem tendsto_intro {F₂ : filter Y} {F₁ : filter X} {f : X → Y}
    (H : ∀ P, eventually P F₂ → eventually (λ x, P (f x)) F₁) :
  tendsto f F₂ F₁ := H

theorem tendsto_dest' {F₂ : filter Y} {F₁ : filter X} {f : X → Y}
    {P : Y → Prop} (H : tendsto f F₂ F₁) (H' : eventually P F₂) :
  eventually P (mapfilter f F₁) := H H'

theorem tendsto_dest {F₂ : filter Y} {F₁ : filter X} {f : X → Y}
    {P : Y → Prop} (H : tendsto f F₂ F₁) (H' : eventually P F₂) :
  eventually (λ x, P (f x)) F₁ := eventually_of_eventually_mapfilter (tendsto_dest' H H')

theorem tendsto_iff' (F₂ : filter Y) (F₁ : filter X) (f : X → Y) :
  tendsto f F₂ F₁ ↔ (∀ P, eventually P F₂ → eventually P (mapfilter f F₁)) :=
iff.refl _

theorem tendsto_iff (F₂ : filter Y) (F₁ : filter X) (f : X → Y) :
  tendsto f F₂ F₁ ↔ (∀ P, eventually P F₂ → eventually (λ x, P (f x)) F₁) :=
iff.refl _

theorem tendsto_comp {f : X → Y} {g : Y → Z} {F₁ : filter X} {F₂ : filter Y} {F₃ : filter Z}
  (Hf : tendsto f F₂ F₁) (Hg : tendsto g F₃ F₂) : tendsto (g ∘ f) F₃ F₁ :=
tendsto_intro (take P, suppose eventually P F₃,
    have eventually (λ y, P (g y)) F₂, from tendsto_dest Hg this,
    show eventually (λ x, P (g (f x))) F₁, from tendsto_dest Hf this)

theorem tendsto_of_le_left {f : X → Y} {F₂ F₂' : filter Y} {F₁ : filter X}
  (HF₂ : F₂ ≤ F₂') (H : tendsto f F₂ F₁) : tendsto f F₂' F₁ :=
take P, suppose eventually P F₂',
have eventually P F₂, from eventually_of_le this HF₂,
show eventually P (mapfilter f F₁), from H this

theorem tendsto_of_le_right {f : X → Y} {F₂ : filter Y} {F₁ F₁' : filter X}
  (HF₁ : F₁' ≤ F₁) (H : tendsto f F₂ F₁) : tendsto f F₂ F₁' :=
take P, suppose eventually P F₂,
have eventually P (mapfilter f F₁), from H this,
show eventually P (mapfilter f F₁'), from eventually_of_le this (mapfilter_le_mapfilter _ HF₁)

theorem tendsto_of_le_of_le {f : X → Y} {F₂ F₂' : filter Y} {F₁ F₁' : filter X}
  (HF₂ : F₂ ≤ F₂') (HF₁ : F₁' ≤ F₁) (H : tendsto f F₂ F₁) : tendsto f F₂' F₁' :=
tendsto_of_le_left HF₂ (tendsto_of_le_right HF₁ H)

theorem tendsto_id {F : filter X} : tendsto (λ x, x) F F :=
take P, assume H, H

theorem tendsto_inf_left {f : X → Y} {F₂ : filter Y} (F₁ : filter X) {F₁' : filter X}
    (H : tendsto f F₂ F₁) :
  tendsto f F₂ (inf F₁ F₁') :=
tendsto_of_le_right !inf_le_left H

theorem tendsto_inf_right {f : X → Y} {F₂ : filter Y} {F₁ : filter X} (F₁' : filter X)
    (H : tendsto f F₂ F₁') :
  tendsto f F₂ (inf F₁ F₁') :=
tendsto_of_le_right !inf_le_right H

theorem tendsto_inf {f : X → Y} {F₂ F₂' : filter Y} {F₁ : filter X}
    (H₁ : tendsto f F₂ F₁) (H₂ : tendsto f F₂' F₁) :
  tendsto f (inf F₂ F₂') F₁ :=
tendsto_intro (take P, suppose eventually P (inf F₂ F₂'),
  obtain S [eSF₂ [T [eTF₂' STsubP]]], from exists_of_eventually_inf this,
  have HS : eventually (λ x, S (f x)) F₁, from tendsto_dest H₁ eSF₂,
  have HT : eventually (λ x, T (f x)) F₁, from tendsto_dest H₂ eTF₂',
  have HST : eventually (λ x, S (f x) ∧ T (f x)) F₁, from eventually_and HS HT,
  have H' : ∀ x, S (f x) ∧ T (f x) → P (f x), from take x, STsubP (f x),
  show eventually (λ x, P (f x)) F₁, from eventually_mono HST H')

theorem tendsto_of_tendsto_inf_left {f : X → Y} {F₂ F₂' : filter Y} {F₁ : filter X}
    (H : tendsto f (inf F₂ F₂') F₁) :
  tendsto f F₂ F₁ :=
tendsto_of_le_left !inf_le_left H

theorem tendsto_of_tendsto_inf_right {f : X → Y} {F₂ F₂' : filter Y} {F₁ : filter X}
    (H : tendsto f (inf F₂ F₂') F₁) :
  tendsto f F₂' F₁ :=
tendsto_of_le_left !inf_le_right H

theorem tendsto_inf_iff (f : X → Y) (F₂ F₂' : filter Y) (F₁ : filter X) :
  tendsto f (inf F₂ F₂') F₁ ↔ tendsto f F₂ F₁ ∧ tendsto f F₂' F₁ :=
iff.intro
  (λ H, and.intro (tendsto_of_tendsto_inf_left H) (tendsto_of_tendsto_inf_right H))
  (λ H, tendsto_inf (and.left H) (and.right H))

theorem tendsto_sup_left {f : X → Y} (F₂ : filter Y) {F₂' : filter Y} {F₁ : filter X}
    (H : tendsto f F₂ F₁) :
  tendsto f (sup F₂ F₂') F₁ :=
tendsto_of_le_left !le_sup_left H

theorem tendsto_sup_right {f : X → Y} (F₂ : filter Y) {F₂' : filter Y} {F₁ : filter X}
    (H : tendsto f F₂' F₁) :
  tendsto f (sup F₂ F₂') F₁ :=
tendsto_of_le_left !le_sup_right H

theorem tendsto_comp_iff_tendsto_mapfilter (f : X → Y) (g : Y → Z) (F₁ : filter X) (F₂ : filter Z) :
  tendsto (g ∘ f) F₂ F₁ ↔ tendsto g F₂ (mapfilter f F₁) :=
!iff.refl

theorem eventually_of_tendsto_principal {f : X → Y} {F : filter X} {s : set Y}
    (H : tendsto f (principal s) F) :
  eventually (λ x, f x ∈ s) F :=
tendsto_dest H (eventually_principal (subset.refl _))

theorem tendsto_principal {f : X → Y} {F : filter X} {s : set Y} (H : eventually (λ x, f x ∈ s) F) :
  tendsto f (principal s) F :=
tendsto_intro (take P, assume ePF,
  have ∀₀ x ∈ s, P x, from subset_of_eventually_principal ePF,
  eventually_mono H (λ x Hfx, this Hfx))

theorem tendsto_principal_iff (f : X → Y) (F : filter X) (s : set Y) :
  tendsto f (principal s) F ↔ eventually (λ x, f x ∈ s) F :=
iff.intro eventually_of_tendsto_principal tendsto_principal

attribute tendsto [irreducible]


/- at_infty -/

section linorderX
  variable [linear_strong_order_pair X]

  definition at_infty : filter X := Inf ((λ x : X, principal '[x, ∞)) ' univ)

  notation `[at ` `∞]`  := at_infty

  private lemma principal_Ici_le_principal_Ici {x₁ x₂ : X} (H : x₁ ≤ x₂) :
    (principal '[x₂, ∞)) ≤ (principal '[x₁, ∞)) :=
  principal_le_principal (show '[x₂, ∞) ⊆ '[x₁, ∞), from λ y Hy, le.trans H Hy)

  theorem eventually_at_infty_intro {P : X → Prop} {x : X} (H : ∀ y, y ≥ x → P y) :
    eventually P [at ∞] :=
  have H' : eventually P (principal '[x, ∞)), from eventually_principal H,
  have principal '[x, ∞) ∈ (λ x : X, principal '[x, ∞)) ' univ, from mem_image_of_mem _ !mem_univ,
  eventually_Inf this H'

  theorem eventually_at_infty_dest {P : X → Prop} [inhabited X]
      (H : eventually P [at ∞]) :
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
    eventually P [at ∞] ↔ ∃ x, ∀ y, y ≥ x → P y :=
  iff.intro eventually_at_infty_dest
    (assume H, obtain x Hx, from H, eventually_at_infty_intro Hx)
end linorderX


/- at_ninfty -/

section linorderX
  variable [linear_strong_order_pair X]

  definition at_ninfty : filter X := Inf ((λ x : X, principal '(-∞, x]) ' univ)

  notation `[at ` `-∞]` := at_ninfty

  private lemma principal_Iic_le_principal_Iic {x₁ x₂ : X} (H : x₁ ≤ x₂) :
    (principal '(-∞, x₁]) ≤ (principal '(-∞, x₂]) :=
  principal_le_principal (show '(-∞, x₁] ⊆ '(-∞, x₂], from λ y Hy, le.trans Hy H)

  theorem eventually_at_ninfty_intro {P : X → Prop} {x : X} (H : ∀ y, y ≤ x → P y) :
    eventually P [at -∞] :=
  have H' : eventually P (principal '(-∞, x]), from eventually_principal H,
  have principal '(-∞, x] ∈ (λ x : X, principal '(-∞, x]) ' univ, from mem_image_of_mem _ !mem_univ,
  eventually_Inf this H'

  theorem eventually_at_ninfty_dest {P : X → Prop} [inhabited X]
      (H : eventually P [at -∞]) :
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
    eventually P [at -∞] ↔ ∃ x, ∀ y, y ≤ x → P y :=
  iff.intro eventually_at_ninfty_dest
    (assume H, obtain x Hx, from H, eventually_at_ninfty_intro Hx)
end linorderX


/- approaches_infty -/

section approaches_infty
  variable [linear_strong_order_pair Y]

  abbreviation approaches_infty (f : X → Y) := tendsto f [at ∞]

  notation f ` ⟶ ` ∞   := tendsto f [at ∞]

  section
  open classical

  theorem approaches_infty_intro {f : X → Y} {F : filter X}
      (H : ∀ y, eventually (λ x, f x ≥ y) F) :
    (f ⟶ ∞) F :=
  tendsto_intro
    (take P, assume eP : eventually P [at ∞],
      if H' : nonempty Y then
        have inhabited Y, from inhabited_of_nonempty H',
        obtain z (Hz : ∀ y, y ≥ z → P y), from eventually_at_infty_dest eP,
        have ∀ x, f x ≥ z → P (f x), from take x, Hz (f x),
        show eventually (λ x, P (f x)) F, from eventually_mono (H z) this
      else
        show eventually (λ x, P (f x)) F, from eventually_of_forall F
          take x, absurd (nonempty.intro (f x)) H')
  end

  theorem approaches_infty_dest {f : X → Y} {F : filter X} (H : (f ⟶ ∞) F) (y : Y) :
    eventually (λ x, f x ≥ y) F :=
  have eventually (λ x, x ≥ y) [at ∞],
    from eventually_at_infty_intro (take x, suppose x ≥ y, this),
  show eventually (λ x, f x ≥ y) F, from tendsto_dest H this

  theorem approaches_infty_iff (f : X → Y) (F : filter X) :
    (f ⟶ ∞) F ↔ ∀ y, eventually (λ x, f x ≥ y) F :=
  iff.intro approaches_infty_dest approaches_infty_intro

  theorem approaches_infty_of_eventually_ge {f g : X → Y} {F : filter X}
      (H : eventually (λ x, f x ≥ g x) F) (H' : (g ⟶ ∞) F) :
    (f ⟶ ∞) F :=
  approaches_infty_intro (take y,
    have eventually (λ x, g x ≥ y) F, from approaches_infty_dest H' y,
    show eventually (λ x, f x ≥ y) F,
      from eventually_mpr H (eventually_mpr this (eventually_of_forall _ (take x, le.trans))))

  theorem id_approaches_infty_at_infty : @id Y ⟶ ∞ [at ∞] := tendsto_id
end approaches_infty


/- approaches_ninfty -/

section approaches_ninfty
  variable [linear_strong_order_pair Y]

  abbreviation approaches_ninfty (f : X → Y) := tendsto f [at -∞]

  notation f ` ⟶ ` -∞  := tendsto f [at -∞]

  section
  open classical

  theorem approaches_ninfty_intro {f : X → Y} {F : filter X}
      (H : ∀ y, eventually (λ x, f x ≤ y) F) :
    (f ⟶ -∞) F :=
  tendsto_intro
    (take P, assume eP : eventually P [at -∞],
      if H' : nonempty Y then
        have inhabited Y, from inhabited_of_nonempty H',
        obtain z (Hz : ∀ y, y ≤ z → P y), from eventually_at_ninfty_dest eP,
        have ∀ x, f x ≤ z → P (f x), from take x, Hz (f x),
        show eventually (λ x, P (f x)) F, from eventually_mono (H z) this
      else
        show eventually (λ x, P (f x)) F, from eventually_of_forall F
          take x, absurd (nonempty.intro (f x)) H')
  end

  theorem approaches_ninfty_dest {f : X → Y} {F : filter X} (H : (f ⟶ -∞) F) (y : Y) :
    eventually (λ x, f x ≤ y) F :=
  have eventually (λ x, x ≤ y) [at -∞],
    from eventually_at_ninfty_intro (take x, suppose x ≤ y, this),
  show eventually (λ x, f x ≤ y) F, from tendsto_dest H this

  theorem approaches_ninfty_iff (f : X → Y) (F : filter X) :
    (f ⟶ -∞) F ↔ ∀ y, eventually (λ x, f x ≤ y) F :=
  iff.intro approaches_ninfty_dest approaches_ninfty_intro

  theorem approaches_ninfty_of_eventually_le {f g : X → Y} {F : filter X}
      (H : eventually (λ x, f x ≤ g x) F) (H' : (g ⟶ -∞) F) :
    (f ⟶ -∞) F :=
  approaches_ninfty_intro (take y,
    have eventually (λ x, g x ≤ y) F, from approaches_ninfty_dest H' y,
    show eventually (λ x, f x ≤ y) F,
      from eventually_mpr H (eventually_mpr this
        (eventually_of_forall _ (take x H₁ H₂, le.trans H₂ H₁))))

  theorem id_approaches_ninfty_at_ninfty : @id Y ⟶ -∞ [at -∞] := tendsto_id
end approaches_ninfty


/- the nhds filter -/

open topology

section nhds_filter
  variables [topology X] {P : X → Prop}

  definition nhds (x : X) : filter X := Inf (principal ' {s | Open s ∧ x ∈ s})

  proposition eventually_nhds_intro {x : X} {s : set X}
      (Os : Open s) (xs : x ∈ s) (H : ∀₀ x ∈ s, P x) :
    eventually P (nhds x) :=
  eventually_Inf (mem_image_of_mem _ (and.intro Os xs)) (eventually_principal H)

  proposition eventually_mem_nhds {x : X} {s : set X} (Os : Open s) (xs : x ∈ s) :
    eventually (λ x, x ∈ s) (nhds x) :=
  eventually_nhds_intro Os xs (λ x Hx, Hx)

  proposition eventually_nhds_dest {x : X} (H : eventually P (nhds x)) :
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
  iff.intro eventually_nhds_dest
    (assume H, obtain s [Os [xs Hs]], from H, eventually_nhds_intro Os xs Hs)
end nhds_filter


/- the at_within filter -/

section at_within
  variables [topology X] {P : X → Prop}

  definition at_within (x : X) (s : set X) : filter X := inf (nhds x) (principal (s \ '{x}))

  notation [at x ` within ` s] := at_within x s

  proposition at_within_le_nhds (x : X) (s : set X) : [at x within s] ≤ nhds x :=
  inf_le_left _ _

  proposition at_within_le_at_within (x : X) {s t : set X} (H : s ⊆ t) :
    [at x within s] ≤ [at x within t] :=
  have s \ '{x} ⊆ t \ '{x}, by rewrite diff_eq; apply inter_subset_inter_right _ H,
  le_inf (inf_le_left _ _) (le.trans !inf_le_right (principal_le_principal this))

  proposition eventually_at_within_intro {x : X} {s t : set X} (Os : Open s) (xs : x ∈ s)
      (Hs : ∀₀ y ∈ s, y ≠ x → y ∈ t → P y) :
    eventually P [at x within t] :=
  have H₁ : eventually (λ y, y ≠ x → y ∈ t → P y) (nhds x),
    from eventually_nhds_intro Os xs Hs,
  eventually_inf H₁ _ (mem_principal _)
    (take y, assume Hy,
      have H : y ∈ t \ '{x}, from and.right Hy,
      have H' : y ≠ x, from suppose y = x,
        have y ∈ '{x}, from mem_singleton_of_eq this,
        show false, from and.right H this,
      show P y, from and.left Hy `y ≠ x` (and.left H))

  proposition eventually_at_within_dest {x : X} {t : set X}
     (H : eventually P [at x within t]) :
    ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y ≠ x → y ∈ t → P y :=
  obtain P₁ [eP₁nhds [P₂ [eP₂princ (H' : P ⊇ P₁ ∩ P₂)]]], from exists_of_eventually_inf H,
  obtain s [Os [xs Hs]], from eventually_nhds_dest eP₁nhds,
  have Ht : ∀₀ y ∈ t \ '{x}, P₂ y, from subset_of_eventually_principal eP₂princ,
  exists.intro s (and.intro Os (and.intro xs
    (take y, assume ys ynex yt,
      have y ∉ '{x}, from assume ymem, ynex (eq_of_mem_singleton ymem),
      show P y, from H' (and.intro (Hs y ys) (Ht (mem_diff yt this))))))

  theorem eventually_at_within_iff (x : X) {s : set X} :
    eventually P [at x within s] ↔ ∃ t, Open t ∧ x ∈ t ∧ ∀₀ y ∈ t, y ≠ x → y ∈ s → P y :=
  iff.intro eventually_at_within_dest
    (assume H, obtain t [Ot [xt Ht]], from H, eventually_at_within_intro Ot xt Ht)

  theorem eventually_at_within_of_subset {x : X} {s t : set X} (ssubt : s ⊆ t)
      (H : eventually P [at x within t]) :
    eventually P [at x within s] :=
  eventually_of_le H (at_within_le_at_within x ssubt)

  abbreviation at_elt (x : X) : filter X := at_within x univ

  notation [at x] := at_elt x

  proposition eventually_at_intro {x : X} {s : set X} (Os : Open s) (xs : x ∈ s)
      (Hs : ∀₀ y ∈ s, y ≠ x → P y) :
    eventually P [at x] :=
  eventually_at_within_intro Os xs (take y, assume ys ynex yuniv, Hs ys ynex)

  proposition eventually_at_dest {x : X} (H : eventually P [at x]) :
    ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y ≠ x → P y :=
  obtain s [Os [xs Hs]], from eventually_at_within_dest H,
  exists.intro s (and.intro Os (and.intro xs (λ y ys ynex, Hs y ys ynex trivial)))

  proposition eventually_at_iff (x : X) :
    eventually P [at x] ↔ ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y ≠ x → P y :=
  iff.intro eventually_at_dest
    (assume H, obtain s [Os [xs Hs]], from H, eventually_at_intro Os xs Hs)

  proposition eventually_at_within_of_eventually_at {x : X} (s : set X) (H : eventually P [at x]) :
    eventually P [at x within s] :=
  eventually_at_within_of_subset (subset_univ s) H

  proposition at_within_eq_of_Open {x : X} {s : set X} (Os : Open s) (xs : x ∈ s) :
    [at x within s] = [at x] :=
  filter.eq (ext (take P, iff.intro
    (assume H,
      obtain t [Ot [xt Ht]], from eventually_at_within_dest H,
      eventually_at_intro (Open_inter Os Ot) (mem_inter xs xt)
        (λ y Hy yne, Ht _ (and.right Hy) yne (and.left Hy)))
    (assume H,
      obtain t [Ot [xt Ht]], from eventually_at_dest H,
      eventually_at_within_intro (Open_inter Os Ot) (mem_inter xs xt)
        (λ y Hy yne ys, Ht _ (and.right Hy) yne))))

  proposition tendsto_at_within_of_subset {f : X → Y} {F : filter Y} {x : X } {s t : set X}
      (ssubt : s ⊆ t) (H : tendsto f F [at x within t]) :
    tendsto f F [at x within s] :=
  tendsto_intro (take P eP,
    have eventually (λ x, P (f x)) [at x within t], from tendsto_dest H eP,
    show eventually (λ x, P (f x)) [at x within s], from eventually_at_within_of_subset ssubt this)
end at_within


/- at_left and at_right -/

section at_left_at_right
  variables [topology X] [linear_strong_order_pair X] {P : X → Prop}

  abbreviation at_left (x : X) : filter X := [at x within '(-∞, x)]
  abbreviation at_right (x : X) : filter X := [at x within '(x, ∞)]

  notation [at x`-]` := at_left x
  notation [at x`+]` := at_right x

  proposition eventually_at_left_intro {x : X} {s : set X} (Os : Open s) (xs : x ∈ s)
      (H : ∀₀ y ∈ s, y < x → P y) :
    eventually P [at x-] :=
  eventually_at_within_intro Os xs (take y, assume ys ynex yltx, H ys yltx)

  proposition eventually_at_left_dest {x : X} (H : eventually P [at x-]) :
    ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y < x → P y :=
  obtain s [Os [xs Hs]], from eventually_at_within_dest H,
  exists.intro s (and.intro Os (and.intro xs
    (take y, assume ys yltx,
      show P y, from Hs y ys (ne_of_lt yltx) yltx)))

  variable (P)
  proposition eventually_at_left_iff (x : X) :
    eventually P [at x-] ↔ ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y < x → P y :=
  iff.intro eventually_at_left_dest
    (take H, obtain s [Os [xs Hs]], from H, eventually_at_left_intro Os xs Hs)

  variable {P}
  proposition eventually_at_right_intro {x : X} {s : set X} (Os : Open s) (xs : x ∈ s)
      (H : ∀₀ y ∈ s, y > x → P y) :
    eventually P [at x+] :=
  eventually_at_within_intro Os xs (take y, assume ys ynex yltx, H ys yltx)

  proposition eventually_at_right_dest {x : X} (H : eventually P [at x+]) :
    ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y > x → P y :=
  obtain s [Os [xs Hs]], from eventually_at_within_dest H,
  exists.intro s (and.intro Os (and.intro xs
    (take y, assume ys yltx,
      show P y, from Hs y ys (ne_of_gt yltx) yltx)))

  variable (P)
  proposition eventually_at_right_iff (x : X) :
    eventually P [at x+] ↔ ∃ s, Open s ∧ x ∈ s ∧ ∀₀ y ∈ s, y > x → P y :=
  iff.intro eventually_at_right_dest
    (take H, obtain s [Os [xs Hs]], from H, eventually_at_right_intro Os xs Hs)
end at_left_at_right


/- approaches -/

section approaches
  variables [topology Y]
  variables {F : filter X} {f : X → Y} {y : Y}

  abbreviation approaches (f : X → Y) (y : Y) : filter X → Prop := tendsto f (nhds y)

  notation f ⟶ y := approaches f y

  proposition approaches_intro (H : ∀ s, Open s → y ∈ s → eventually (λ x, f x ∈ s) F) :
    (f ⟶ y) F :=
  tendsto_intro
    (take P, assume eventuallyP,
      obtain s [Os [(ys : y ∈ s) (H' : ∀₀ y' ∈ s, P y')]],
        from eventually_nhds_dest eventuallyP,
      show eventually (λ x, P (f x)) F, from eventually_mono (H s Os ys) (λ x Hx, H' Hx))

  proposition approaches_elim (H : (f ⟶ y) F) {s : set Y} (Os : Open s) (ys : y ∈ s) :
    eventually (λ x, f x ∈ s) F :=
  tendsto_dest H (eventually_mem_nhds Os ys)

  variables (F f y)
  proposition approaches_iff : (f ⟶ y) F ↔ (∀ s, Open s → y ∈ s → eventually (λ x, f x ∈ s) F) :=
  iff.intro approaches_elim approaches_intro

  proposition tendsto_comp_of_approaches_of_tendsto_at_within
      {f : X → Y} {g : Y → Z} {s : set Y} {y : Y} {F₁ : filter X} {F₃ : filter Z}
      (Hf₁ : (f ⟶ y) F₁) (Hf₂ : eventually (λ x, f x ∈ s ∧ f x ≠ y) F₁)
      (Hg : tendsto g F₃ [at y within s]) :
    tendsto (g ∘ f) F₃ F₁ :=
  have eventually (λ x, f x ∈ s \ '{y}) F₁,
    from eventually_congr (take x, by rewrite [mem_diff_iff, mem_singleton_iff]) Hf₂,
  have tendsto f [at y within s] F₁, from tendsto_inf Hf₁ (tendsto_principal this),
  tendsto_comp this Hg

  proposition tendsto_comp_of_approaches_of_tendsto_at
      {f : X → Y} {g : Y → Z} {y : Y} {F₁ : filter X} {F₃ : filter Z}
      (Hf₁ : (f ⟶ y) F₁) (Hf₂ : eventually (λ x, f x ≠ y) F₁)
      (Hg : tendsto g F₃ [at y]) :
    tendsto (g ∘ f) F₃ F₁ :=
  have eventually (λ x, f x ∈ univ ∧ f x ≠ y) F₁,
    from eventually_congr (take x, by rewrite [mem_univ_iff, true_and]) Hf₂,
  tendsto_comp_of_approaches_of_tendsto_at_within Hf₁ this Hg

  proposition approaches_constant : ((λ x, y) ⟶ y) F :=
  begin
    apply approaches_intro,
    intro s Hs Hys,
    have H : (λ x : X, y ∈ s) = (λ x : X, true), from funext (λ x, by rewrite classical.eq_true; exact Hys),
    rewrite H,
    apply eventually_true
  end

end approaches

/-
  Properties of convergence at infty on nat and real (and more generally ordered semigroups)
-/

section
  open nat

  proposition eventually_at_infty_of_eventually_succ_at_infty {P : ℕ → Prop}
    (H : eventually (λ n, P (succ n)) [at ∞]) : eventually P [at ∞] :=
  obtain x (Hx : ∀ y, y ≥ x → P (succ y)), from eventually_at_infty_dest H,
  eventually_at_infty_intro (take y, suppose y > x,
    have y ≥ succ x, from succ_le_of_lt this,
    have pred y ≥ pred (succ x), from pred_le_pred this,
    have pred y ≥ x, by rewrite pred_succ at this; assumption,
    have P (succ (pred y)), from Hx _ this,
    show P y,
      by rewrite (succ_pred_of_pos (lt_of_lt_of_le !zero_lt_succ `succ x ≤ y`)) at this; assumption)

  proposition eventually_succ_at_infty {P : ℕ → Prop}
    (H : eventually (λ n, P n) [at ∞]) : eventually (λ n, P (succ n)) [at ∞] :=
  obtain x (Hx : ∀ y, y ≥ x → P y), from eventually_at_infty_dest H,
  eventually_at_infty_intro (take y, suppose y > x,
    show P (succ y), from Hx _ (le_of_lt (lt.trans this !lt_succ_self)))

  proposition eventually_succ_at_infty_iff (P : ℕ → Prop) :
    (eventually (λ n, P (succ n)) [at ∞]) ↔ (eventually P [at ∞]) :=
  iff.intro eventually_at_infty_of_eventually_succ_at_infty eventually_succ_at_infty

  proposition tendsto_succ_at_infty {f : ℕ → Y} {F : filter Y} (H : tendsto f F [at ∞]) :
    tendsto (λ n, f (succ n)) F [at ∞] :=
  tendsto_intro (take P, suppose eventually P F,
    eventually_succ_at_infty (tendsto_dest H this))

  proposition tendsto_at_infty_of_tendsto_succ_at_infty {f : ℕ → Y} {F : filter Y}
      (H : tendsto (λ n, f (succ n)) F [at ∞]) :
    tendsto f F [at ∞] :=
  tendsto_intro (take P, suppose eventually P F,
    eventually_at_infty_of_eventually_succ_at_infty (tendsto_dest H this))

  proposition tendsto_succ_at_infty_iff (f : ℕ → Y) (F : filter Y) :
    (tendsto (λ n, f (succ n)) F [at ∞]) ↔ (tendsto f F [at ∞]) :=
  iff.intro tendsto_at_infty_of_tendsto_succ_at_infty tendsto_succ_at_infty

  proposition succ_approaches_infty_at_infty : (λ n, succ n) ⟶ ∞ [at ∞] :=
  tendsto_succ_at_infty id_approaches_infty_at_infty

  -- alterantive proof:
  --  approaches_infty_intro (take n,
  --    eventually_at_infty_intro (take y, suppose y ≥ n,
  --      show succ y ≥ n, from le.trans this (le_of_lt (lt_succ_self y))))

  -- another alternative proof:
  --  approaches_infty_of_eventually_ge
  --    (eventually_of_forall _ (λ x, le_of_lt (lt_succ_self x))
  --    id_approaches_infty_at_infty

  -- TODO: for these next proofs: we should unify nat and group cases, with a class
  -- with the axiom x ≤ y → y - x + x = y.
  -- in the meanwhile, put ' on these versions

  -- TODO: add_left versions

  proposition eventually_at_infty_of_eventually_add_right_at_infty' {P : ℕ → Prop} {k : ℕ}
    (H : eventually (λ n, P (n + k)) [at ∞]) : eventually P [at ∞] :=
  obtain x (Hx : ∀ y, y ≥ x → P (y + k)), from eventually_at_infty_dest H,
  eventually_at_infty_intro (take y, suppose y ≥ x + k,
    have y - k ≥ x, from nat.le_sub_of_add_le this,
    have H' : P (y - k + k), from Hx _ this,
    have y ≥ k, from le.trans !le_add_left `x + k ≤ y`,
    show P y, by rewrite [nat.sub_add_cancel this at H']; exact H')

  proposition eventually_add_right_at_infty' {P : ℕ → Prop} (k : ℕ)
    (H : eventually (λ n, P n) [at ∞]) : eventually (λ n, P (n + k)) [at ∞] :=
  obtain x (Hx : ∀ y, y ≥ x → P y), from eventually_at_infty_dest H,
  eventually_at_infty_intro (take y, suppose y ≥ x,
    have y + k ≥ x, from le.trans this !le_add_right,
    show P (y + k), from Hx _ this)

  proposition eventually_add_right_at_infty_iff' (k : ℕ) (P : ℕ → Prop) :
    (eventually (λ n, P (n + k)) [at ∞]) ↔ (eventually P [at ∞]) :=
  iff.intro eventually_at_infty_of_eventually_add_right_at_infty' (eventually_add_right_at_infty' k)

  proposition tendsto_add_right_at_infty' {f : ℕ → Y} {F : filter Y}
      (H : tendsto f F [at ∞]) (k : ℕ) :
    tendsto (λ n, f (n + k)) F [at ∞] :=
  tendsto_intro (take P, suppose eventually P F,
    eventually_add_right_at_infty' k (tendsto_dest H this))

  proposition tendsto_at_infty_of_tendsto_add_right_at_infty' {f : ℕ → Y} {F : filter Y} {k : ℕ}
      (H : tendsto (λ n, f (n + k)) F [at ∞]) :
    tendsto f F [at ∞] :=
  tendsto_intro (take P, suppose eventually P F,
    eventually_at_infty_of_eventually_add_right_at_infty' (tendsto_dest H this))

  proposition tendsto_add_right_at_infty_iff' (f : ℕ → Y) (F : filter Y) (k : ℕ) :
    (tendsto (λ n, f (n + k)) F [at ∞]) ↔ (tendsto f F [at ∞]) :=
  iff.intro tendsto_at_infty_of_tendsto_add_right_at_infty' (λ H, tendsto_add_right_at_infty' H k)
end

section
  -- TODO: move to algebra?
  private proposition inhabited_of_has_zero [trans_instance] (H : has_zero X) : inhabited X :=
  inhabited.mk 0

  variable [decidable_linear_ordered_comm_group X]

  proposition eventually_at_infty_of_eventually_add_right_at_infty {P : X → Prop} {k : X}
    (H : eventually (λ n, P (n + k)) [at ∞]) : eventually P [at ∞] :=
  obtain x (Hx : ∀ y, y ≥ x → P (y + k)), from eventually_at_infty_dest H,
  eventually_at_infty_intro (take y, suppose y ≥ x + k,
    have y - k ≥ x, from le_sub_right_of_add_le this,
    have H' : P (y - k + k), from Hx _ this,
    show P y, by rewrite [sub_add_cancel at H']; exact H')

  proposition eventually_add_right_at_infty {P : X → Prop} (k : X)
    (H : eventually (λ n, P n) [at ∞]) : eventually (λ n, P (n + k)) [at ∞] :=
  have eventually (λ n, P (n + -k + k)) [at ∞],
    from eventually_congr (take x, by rewrite [neg_add_cancel_right]) H,
  eventually_at_infty_of_eventually_add_right_at_infty this

  proposition eventually_add_right_at_infty_iff (k : X) (P : X → Prop) :
    (eventually (λ n, P (n + k)) [at ∞]) ↔ (eventually P [at ∞]) :=
  iff.intro eventually_at_infty_of_eventually_add_right_at_infty (eventually_add_right_at_infty k)

  proposition tendsto_add_right_at_infty {f : X → Y} {F : filter Y}
      (H : tendsto f F [at ∞]) (k : X) :
    tendsto (λ n, f (n + k)) F [at ∞] :=
  tendsto_intro (take P, suppose eventually P F,
    eventually_add_right_at_infty k (tendsto_dest H this))

  proposition tendsto_at_infty_of_tendsto_add_right_at_infty {f : X → Y} {F : filter Y} {k : X}
      (H : tendsto (λ n, f (n + k)) F [at ∞]) :
    tendsto f F [at ∞] :=
  tendsto_intro (take P, suppose eventually P F,
    eventually_at_infty_of_eventually_add_right_at_infty (tendsto_dest H this))

  proposition tendsto_add_right_at_infty_iff (f : X → Y) (F : filter Y) (k : X) :
    (tendsto (λ n, f (n + k)) F [at ∞]) ↔ (tendsto f F [at ∞]) :=
  iff.intro tendsto_at_infty_of_tendsto_add_right_at_infty (λ H, tendsto_add_right_at_infty H k)
end

end topology
