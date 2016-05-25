/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Gross, Jeremy Avigad

Continuous functions.
-/
import theories.topology.basic algebra.category ..move .limit
open algebra eq.ops set topology function category sigma.ops

namespace topology

/- continuity on a set -/

variables {X Y Z : Type} [topology X] [topology Y] [topology Z]

definition continuous_on (f : X → Y) (s : set X) : Prop :=
  ∀ ⦃t : set Y⦄, Open t → (∃ u : set X, Open u ∧ u ∩ s = f '- t ∩ s)

theorem exists_Open_of_continous_on {f : X → Y} {s : set X} {t : set Y} (Ot : Open t)
    (H : continuous_on f s) :
  ∃ u : set X, Open u ∧ u ∩ s = f '- t ∩ s := H Ot

theorem Open_preimage_inter_of_continuous_on {f : X → Y} {s : set X} (Os : Open s)
    (Hcont : continuous_on f s) {t : set Y} (Ot : Open t) :
  Open (f '- t ∩ s) :=
obtain u [Ou Hu], from Hcont Ot,
by rewrite[-Hu]; exact Open_inter Ou Os

theorem continuous_on_of_forall_open {f : X → Y} {s : set X}
    (H : ∀ t, Open t → Open (f '- t ∩ s)) :
  continuous_on f s :=
take t, assume Ot,
have f '- t ∩ s ∩ s = f '- t ∩ s, by rewrite [inter_assoc, inter_self],
exists.intro (f '- t ∩ s) (and.intro (H t Ot) this)

theorem Open_preimage_of_continuous_on {f : X → Y} {s : set X} (Opens : Open s)
    (contfs : continuous_on f s) {t : set Y} (Ot : Open t) (Hpre : f '- t ⊆ s) :
  Open (f '- t) :=
have f '- t ∩ s = f '- t, from inter_eq_self_of_subset Hpre,
show Open (f '- t),
  by rewrite -this; apply Open_preimage_inter_of_continuous_on Opens contfs Ot

theorem exists_closed_of_continuous_on {f : X → Y} {s : set X}
    (contfs : continuous_on f s) {t : set Y} (clt : closed t) :
  ∃ u, closed u ∧ u ∩ s = f '- t ∩ s :=
obtain v [Ov (Hv  : v ∩ s = f '- -t ∩ s)], from contfs clt,
have -v ∩ s = f '- t ∩ s,
  from inter_eq_inter_of_compl_inter_eq_compl_inter (by rewrite [compl_compl, Hv]),
show ∃ u, closed u ∧ u ∩ s = f '- t ∩ s,
  from exists.intro (-v) (and.intro (closed_compl Ov) this)

theorem continuous_on_of_forall_closed' {f : X → Y} {s : set X}
    (H : ∀ t, closed t → ∃ u, closed u ∧ u ∩ s = f '- t ∩ s) :
  continuous_on f s :=
take t : set Y, assume Ot : Open t,
obtain (v : set X) [(clv : closed v) (Hv : v ∩ s = f '- (-t) ∩ s)], from H (-t) (closed_compl Ot),
have (-v) ∩ s = f '- t ∩ s,
  from inter_eq_inter_of_compl_inter_eq_compl_inter (by rewrite [compl_compl, Hv]),
show ∃ u, Open u ∧ u ∩ s = f '- t ∩ s,
  from exists.intro (-v) (and.intro clv this)

theorem continuous_on_of_forall_closed {f : X → Y} {s : set X} (closeds : closed s)
  (H : ∀ B, closed B → closed (f '- B ∩ s)) : continuous_on f s :=
continuous_on_of_forall_closed'
  (λ B HB, exists.intro _ (and.intro (H B HB) (by rewrite [inter_assoc, inter_self])))

theorem closed_preimage_inter_of_continuous_on {f : X → Y} {s : set Y} (cls : closed s)
    {t : set X} (clt : closed t) (contft : continuous_on f t) :
  closed (f '- s ∩ t) :=
obtain u [clu Hu], from exists_closed_of_continuous_on contft cls,
by rewrite [-Hu]; exact (closed_inter clu clt)

theorem continuous_on_subset {s t : set X} {f : X → Y} (Hs : continuous_on f s) (ts : t ⊆ s) :
  continuous_on f t :=
take u, assume Ou,
obtain v [Ov Hv], from Hs Ou,
have v ∩ t = f '- u ∩ t, by rewrite [-inter_eq_self_of_subset_right ts, -*inter_assoc, Hv],
show ∃ v, Open v ∧ v ∩ t = f '- u ∩ t, from exists.intro v (and.intro Ov this)

theorem continous_on_union_of_closed {f : X → Y} {s t : set X} (cls : closed s) (clt : closed t)
    (contsf : continuous_on f s) (conttf : continuous_on f t) :
  continuous_on f (s ∪ t) :=
have ∀ u, closed u → closed (f '- u ∩ (s ∪ t)), from
  begin
    intro u clu,
    rewrite [inter_distrib_left],
    exact closed_union (closed_preimage_inter_of_continuous_on clu cls contsf)
      (closed_preimage_inter_of_continuous_on clu clt conttf)
  end,
show continuous_on f (s ∪ t),
  from continuous_on_of_forall_closed (closed_union cls clt) this

theorem continuous_on_empty (f : X → Y) : continuous_on f ∅ :=
continuous_on_of_forall_open
  (take B, assume OpenB, by rewrite[inter_empty]; apply Open_empty)

theorem continuous_on_union {f : X → Y} {s t : set X}
    (Opens : Open s) (Opent : Open t) (contsf : continuous_on f s) (conttf : continuous_on f t) :
  continuous_on f (s ∪ t) :=
continuous_on_of_forall_open
  (take B, assume OpenB,
    have Open (f '- B ∩ s), from Open_preimage_inter_of_continuous_on Opens contsf OpenB,
    have Open (f '- B ∩ t), from Open_preimage_inter_of_continuous_on Opent conttf OpenB,
    show Open (f '- B ∩ (s ∪ t)),
      by rewrite [inter_distrib_left]; apply Open_union; assumption; assumption)

theorem continuous_on_id (s : set X) :  continuous_on (@id X) s :=
λ B OpB, exists.intro B (and.intro OpB (by rewrite preimage_id))

theorem continuous_on_comp {s : set X} {f : X → Y} {g : Y → Z}
  (Hf : continuous_on f s) (Hg : continuous_on g (f ' s)) : continuous_on (g ∘ f) s :=
take t, assume Ot,
obtain (u : set Y) [(Ou : Open u) (Hu : u ∩ f ' s = g '- t ∩ f ' s)], from Hg Ot,
obtain (v : set X) [(Ov : Open v) (Hv : v ∩ s = f '- u ∩ s)], from Hf Ou,
have s ⊆ f '- (f ' s), from subset_preimage_image s f,
have f '- (u ∩ f ' s) ∩ s = f '- (g '- t ∩ f ' s) ∩ s, by rewrite Hu,
have f '- u ∩ s = f '- (g '- t) ∩ s,
  begin
    revert this,
    rewrite [*preimage_inter, *inter_assoc, *inter_eq_self_of_subset_right `s  ⊆ f '- (f ' s)`],
    intro H, exact H
  end,
show ∃ v, Open v ∧ v ∩ s = (g ∘ f) '- t ∩ s,
  from exists.intro v (and.intro Ov (eq.trans Hv this))

theorem continuous_on_comp' {s : set X} {t : set Y} {f : X → Y} {g : Y → Z}
  (Hf : continuous_on f s) (Hg : continuous_on g t) (H : f ' s ⊆ t) : continuous_on (g ∘ f) s :=
continuous_on_comp Hf (continuous_on_subset Hg H)

section
  open classical

  theorem continuous_on_singleton (f : X → Y) (x : X) :
    continuous_on f '{x} :=
  take s, assume Ops,
  if Hx : x ∈ f '- s then
    have '{x} ⊆ f '- s, from singleton_subset_of_mem Hx,
    exists.intro univ (and.intro Open_univ
      (by rewrite [univ_inter, inter_eq_self_of_subset_right this]))
  else
    have f '- s ∩ '{x} = ∅,
      from eq_empty_of_forall_not_mem
        (take y, assume ymem,
          obtain (Hy : y ∈ f '- s) (Hy' : y ∈ '{x}), from ymem,
          have y = x, from eq_of_mem_singleton Hy',
          show false, from Hx (by rewrite -this; apply Hy)),
    exists.intro ∅ (and.intro Open_empty (by rewrite [this, empty_inter]))

  theorem continuous_on_const (c : Y) (s : set X) :
    continuous_on (λ x : X, c) s :=
  take s, assume Ops,
  if cs : c ∈ s then
    have (λx, c) '- s = @univ X, from eq_univ_of_forall (take x, mem_preimage cs),
    exists.intro univ (and.intro Open_univ (by rewrite this))
  else
    have (λx, c) '- s = (∅ : set X),
      from eq_empty_of_forall_not_mem (take x, assume H, cs (mem_of_mem_preimage H)),
    exists.intro ∅ (and.intro Open_empty (by rewrite this))
end


/- pointwise continuity on a set -/

definition continuous_at_on (f : X → Y) (x : X) (s : set X) : Prop :=
∀ ⦃t : set Y⦄, Open t → f x ∈ t → ∃ u, Open u ∧ x ∈ u ∧ u ∩ s ⊆ f '- t

theorem continuous_at_on_of_continuous_on {f : X → Y} {s : set X}
    (H : continuous_on f s) ⦃x : X⦄ (xs : x ∈ s) :
  continuous_at_on f x s :=
take u, assume (Ou : Open u) (fxu : f x ∈ u),
obtain (t : set X) [(Ot : Open t) (Ht : t ∩ s = f '- u ∩ s)], from H Ou,
have x ∈ f '- u ∩ s, from and.intro fxu xs,
have x ∈ t, by rewrite [-Ht at this]; exact and.left this,
exists.intro t (and.intro Ot (and.intro this (by rewrite Ht; apply inter_subset_left)))

section
open classical

theorem continuous_on_of_forall_continuous_at_on {f : X → Y} {s : set X}
    (H : ∀ x, continuous_at_on f x s) :
  continuous_on f s :=
take t, assume Ot : Open t,
have H₁ : ∀₀ x ∈ f '- t, ∃ u', Open u' ∧ x ∈ u' ∧ u' ∩ s ⊆ f '- t,
  from λ x xmem, H x Ot (mem_of_mem_preimage xmem),
let u := ⋃₀ {u' | ∃ x (Hx : x ∈ f '- t), u' = some (H₁ Hx) } in
have Open u, from Open_sUnion
  (take u', assume Hu',
    obtain x (Hx : x ∈ f '- t) (u'eq : u' = some (H₁ Hx)), from Hu',
    show Open u', by rewrite u'eq; apply and.left (some_spec (H₁ Hx))),
have Hu₁ : u ∩ s ⊆ f '- t, from
  take x, assume Hx,
  obtain xu xs, from Hx,
  obtain u' [[x' (Hx' : x' ∈ f '- t) (u'eq : u' = some (H₁ Hx'))] (xu' : x ∈ u')], from xu,
  have u' ∩ s ⊆ f '- t, by rewrite u'eq; exact and.right (and.right (some_spec (H₁ Hx'))),
  show x ∈ f '- t, from this (and.intro xu' xs),
have Hu₂ : f '- t ∩ s ⊆ u, from
  take x, assume Hx : x ∈ f '- t ∩ s,
  obtain xft xs, from Hx,
  let u' := some (H₁ xft) in
  have x ∈ u', from and.left (and.right (some_spec (H₁ xft))),
  show x ∈ u, from exists.intro u' (and.intro (exists.intro x (exists.intro xft rfl)) this),
show ∃ u, Open u ∧ u ∩ s = f '- t ∩ s,
  from exists.intro u (and.intro `Open u` (inter_eq_inter_right Hu₁ Hu₂))

end


/- continuity -/

definition continuous (f : X → Y) : Prop := ∀ ⦃s : set Y⦄, Open s → Open (f '- s)

theorem continuous_of_continuous_on_univ {f : X → Y} (H : continuous_on f univ) : continuous f :=
λ s Os, by rewrite [-inter_univ]; exact Open_preimage_inter_of_continuous_on Open_univ H Os

theorem continuous_on_of_continuous {f : X → Y} (s : set X) (H : continuous f) :
  continuous_on f s :=
take t, assume Ot, exists.intro (f '- t) (and.intro (H Ot) rfl)

theorem continuous_on_univ_of_continuous {f : X → Y} (H : continuous f) : continuous_on f univ :=
continuous_on_of_continuous univ H

theorem continuous_iff (f : X → Y) : continuous f ↔ continuous_on f univ :=
iff.intro continuous_on_univ_of_continuous continuous_of_continuous_on_univ

theorem Open_preimage_of_continuous {f : X → Y} (H : continuous f) ⦃s : set Y⦄ (Os : Open s) :
  Open (f '- s) := H Os

theorem closed_preimage_of_continuous {f : X → Y} (H : continuous f) {s : set Y} (cls : closed s) :
  closed (f '- s) :=
by rewrite [↑closed, -preimage_compl]; exact H cls

theorem continuous_id : continuous (@id X) :=
λ s Os, Os

theorem continuous_comp {f : X → Y} {g : Y → Z}
  (Hf : continuous f) (Hg : continuous g) : continuous (g ∘ f) :=
λ s Os, Hf (Hg Os)

theorem continuous_const (c : Y) : continuous (λ x : X, c) :=
continuous_of_continuous_on_univ (continuous_on_const c univ)


/- continuity at a point -/

definition continuous_at (f : X → Y) (x : X) : Prop :=
∀ ⦃t : set Y⦄, Open t → f x ∈ t → ∃ u, Open u ∧ x ∈ u ∧ u ⊆ f '- t

theorem continuous_at_of_continuous_at_on {f : X → Y} {x : X} {s : set X}
    (Os : Open s) (xs : x ∈ s) (H : continuous_at_on f x s) :
  continuous_at f x :=
take t, assume Ot fxt,
obtain u Ou xu xssub, from H Ot fxt,
exists.intro (u ∩ s) (and.intro (Open_inter Ou Os)
  (and.intro (and.intro xu xs) xssub))

theorem continuous_at_of_continuous_at_on_univ {f : X → Y} {x : X}
    (H : continuous_at_on f x univ) :
  continuous_at f x :=
continuous_at_of_continuous_at_on Open_univ !mem_univ H

theorem continuous_at_on_univ_of_continuous_at {f : X → Y} {x : X}
    (H : continuous_at f x) :
  continuous_at_on f x univ :=
take t, assume Ot fxt,
obtain u Ou xu usub, from H Ot fxt,
have u ∩ univ ⊆ f '- t, by rewrite inter_univ; apply usub,
exists.intro u (and.intro Ou (and.intro xu this))

theorem continuous_at_iff_continuous_at_on_univ (f : X → Y) (x : X) :
  continuous_at f x ↔ continuous_at_on f x univ :=
iff.intro continuous_at_on_univ_of_continuous_at continuous_at_of_continuous_at_on_univ

theorem continuous_of_forall_continuous_at {f : X → Y} (H : ∀ x : X, continuous_at f x) :
        continuous f :=
  begin
    apply continuous_of_continuous_on_univ,
    apply continuous_on_of_forall_continuous_at_on,
    intro,
    apply continuous_at_on_univ_of_continuous_at,
    apply H
  end

theorem forall_continuous_at_of_continuous {f : X → Y} (H : continuous f) :
        ∀ x : X, continuous_at f x :=
  begin
    intro,
    apply continuous_at_of_continuous_at_on_univ,
    apply continuous_at_on_of_continuous_on,
    apply continuous_on_univ_of_continuous H,
    apply mem_univ
  end

section limit
open set
theorem tendsto_at_of_continuous_at {f : X → Y} {x : X} (H : continuous_at f x) :
        (f ⟶ f x) (nhds x) :=
  begin
    apply approaches_intro,
    intro s HOs Hfxs,
    cases H HOs Hfxs with u Hu,
    apply eventually_nhds_intro,
    exact and.left Hu,
    exact and.left (and.right Hu),
    intro x' Hx',
    apply @mem_of_mem_preimage _ _ f,
    apply and.right (and.right Hu),
    exact Hx'
  end

theorem continuous_at_of_tendsto_at  {f : X → Y} {x : X} (H : (f ⟶ f x) (nhds x)) :
        continuous_at f x :=
  begin
    intro s HOs Hfxs,
    cases eventually_nhds_dest (approaches_elim H HOs Hfxs) with u Hu,
    existsi u,
    split,
    exact and.left Hu,
    split,
    exact and.left (and.right Hu),
    intro x Hx,
    apply mem_preimage,
    apply and.right (and.right Hu),
    apply Hx
  end

end limit

/- The Category TOP -/

section TOP
open subtype

private definition TOP_hom (A B : TopologicalSpace) : Type :=
{f : A → B | continuous f}

private definition TOP_ID {A : TopologicalSpace} : TOP_hom A A :=
subtype.tag (@id A) continuous_id

private definition TOP_comp ⦃ A B C : TopologicalSpace ⦄ (g : TOP_hom B C) (f : TOP_hom A B) :
  TOP_hom A C :=
subtype.tag (elt_of g ∘ elt_of f)
  (continuous_comp (subtype.has_property f) (subtype.has_property g))

private theorem TOP_assoc ⦃A B C D : TopologicalSpace⦄
    (h : TOP_hom C D) (g : TOP_hom B C) (f : TOP_hom A B) :
  TOP_comp h (TOP_comp g f) = TOP_comp (TOP_comp h g) f :=
subtype.eq rfl

private theorem id_left ⦃A B : TopologicalSpace ⦄ (f : TOP_hom A B) : TOP_comp TOP_ID f = f :=
subtype.eq rfl

private theorem id_right ⦃A B : TopologicalSpace ⦄ (f : TOP_hom A B) : TOP_comp f TOP_ID = f :=
subtype.eq rfl

definition TOP [reducible] [trans_instance] : category TopologicalSpace :=
⦃ category,
  hom := TOP_hom,
  comp := TOP_comp,
  ID := @TOP_ID,
  assoc := TOP_assoc,
  id_left := id_left,
  id_right := id_right
⦄

end TOP

end topology
