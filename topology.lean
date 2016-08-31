/-
Copyright (c) 2015 Jacob Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Gross, Jeremy Avigad

Open and closed sets, seperation axioms and generator topologies.
-/
import data.set data.nat
open algebra eq.ops set nat

/- some useful things involving sets -- to move to data.sets -/

prefix `⋃₀`:110 := sUnion
notation `⋃` binders, r:(scoped f, Union f) := r
notation `⋃` binders `∈` s, r:(scoped f, bUnion s f) := r
prefix `⋂₀`:110 := sInter
notation `⋂` binders, r:(scoped f, Inter f) := r
notation `⋂` binders `∈` s, r:(scoped f, bInter s f) := r

theorem comp_empty {X : Type} : -(∅ : set X) = univ :=
ext (take x, iff.intro (assume H, trivial) (assume H, not_false))

theorem comp_union {X : Type} (s t : set X) : -(s ∪ t) = -s ∩ -t :=
ext (take x, !not_or_iff_not_and_not)

section
  open classical

  theorem comp_comp {X : Type} (s : set X) : -(-s) = s :=
  ext (take x, !not_not_iff)

  theorem comp_inter {X : Type} (s t : set X) : -(s ∩ t) = -s ∪ -t :=
  ext (take x, !not_and_iff_not_or_not)

  theorem comp_univ {X : Type} : -(univ : set X) = ∅ :=
  by rewrite [-comp_empty, comp_comp]
end

theorem comp_eq_univ_diff {X : Type} (s : set X) : -s = univ \ s :=
ext (take x, iff.intro (assume H, and.intro trivial H) (assume H, and.right H))

theorem insert_eq {X : Type} (x : X) (s : set X) : insert x s = '{x} ∪ s :=
ext (take y, iff.intro
  (suppose y ∈ insert x s,
    or.elim this (suppose y = x, or.inl (or.inl this)) (suppose y ∈ s, or.inr this))
  (suppose y ∈ '{x} ∪ s,
    or.elim this
      (suppose y ∈ '{x}, or.inl (eq_of_mem_singleton this))
      (suppose y ∈ s, or.inr this)))

theorem mem_sUnion {X : Type} {x : X} {t : set X} {S : set (set X)} (Hx : x ∈ t) (Ht : t ∈ S) :
  x ∈ ⋃₀ S :=
exists.intro t (and.intro Ht Hx)

theorem Union_eq_sUnion_image {X I : Type} (s : I → set X) : (⋃ i, s i) = ⋃₀ (s '[univ]) :=
ext (take x, iff.intro
  (suppose x ∈ Union s,
    obtain i (Hi : x ∈ s i), from this,
    mem_sUnion Hi (mem_image_of_mem s trivial))
  (suppose x ∈ sUnion (s '[univ]),
    obtain t [(Ht : t ∈ s '[univ]) (Hx : x ∈ t)], from this,
    obtain i [univi (Hi : s i = t)], from Ht,
    exists.intro i (show x ∈ s i, by rewrite Hi; apply Hx)))

theorem Inter_eq_sInter_image {X I : Type} (s : I → set X) : (⋂ i, s i) = ⋂₀ (s '[univ]) :=
ext (take x, iff.intro
  (assume H : x ∈ Inter s,
    take t,
    suppose t ∈ s '[univ],
    obtain i [univi (Hi : s i = t)], from this,
    show x ∈ t, by rewrite -Hi; exact H i)
  (assume H : x ∈ ⋂₀ (s '[univ]),
    take i,
    have s i ∈ s '[univ], from mem_image_of_mem s trivial,
    show x ∈ s i, from H this))

theorem sUnion_empty {X : Type} : ⋃₀ ∅ = (∅ : set X) :=
eq_empty_of_forall_not_mem
  (take x, suppose x ∈ sUnion ∅,
    obtain t [(Ht : t ∈ ∅) Ht'], from this,
    show false, from Ht)

theorem sInter_empty {X : Type} : ⋂₀ ∅ = (univ : set X) :=
eq_univ_of_forall (λ x s H, false.elim H)

theorem sUnion_singleton {X : Type} (s : set X) : ⋃₀ '{s} = s :=
ext (take x, iff.intro
  (suppose x ∈ sUnion '{s},
    obtain u [(Hu : u ∈ '{s}) (xu : x ∈ u)], from this,
    have u = s, from eq_of_mem_singleton Hu,
    show x ∈ s, using this, by rewrite -this; apply xu)
  (suppose x ∈ s,
    mem_sUnion this (mem_singleton s)))

theorem sInter_singleton {X : Type} (s : set X) : ⋂₀ '{s} = s :=
ext (take x, iff.intro
  (suppose x ∈ ⋂₀ '{s}, show x ∈ s, from this (mem_singleton s))
  (suppose x ∈ s, take u, suppose u ∈ '{s},
    show x ∈ u, by+ rewrite [eq_of_mem_singleton this]; assumption))

theorem sUnion_union {X : Type} (S T : set (set X)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T :=
ext (take x, iff.intro
  (suppose x ∈ sUnion (S ∪ T),
    obtain u [(Hu : u ∈ S ∪ T) (xu : x ∈ u)], from this,
    or.elim Hu
      (assume uS, or.inl (mem_sUnion xu uS))
      (assume uT, or.inr (mem_sUnion xu uT)))
  (suppose x ∈ sUnion S ∪ sUnion T,
    or.elim this
      (suppose x ∈ sUnion S,
        obtain u [(uS : u ∈ S) (xu : x ∈ u)], from this,
        mem_sUnion xu (or.inl uS))
      (suppose x ∈ sUnion T,
        obtain u [(uT : u ∈ T) (xu : x ∈ u)], from this,
        mem_sUnion xu (or.inr uT))))

theorem sInter_union {X : Type} (S T : set (set X)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
ext (take x, iff.intro
  (assume H : x ∈ ⋂₀ (S ∪ T),
    and.intro (λ u uS, H (or.inl uS)) (λ u uT, H (or.inr uT)))
  (assume H : x ∈ ⋂₀ S ∩ ⋂₀ T,
    take u, suppose u ∈ S ∪ T, or.elim this (λ uS, and.left H u uS) (λ uT, and.right H u uT)))

theorem sUnion_insert {X : Type} (s : set X) (T : set (set X)) :
  ⋃₀ (insert s T) = s ∪ ⋃₀ T :=
by rewrite [insert_eq, sUnion_union, sUnion_singleton]

theorem sInter_insert {X : Type} (s : set X) (T : set (set X)) :
  ⋂₀ (insert s T) = s ∩ ⋂₀ T :=
by rewrite [insert_eq, sInter_union, sInter_singleton]

theorem mem_image_complement {X : Type} (t : set X) (S : set (set X)) :
  t ∈ complement '[S] ↔ -t ∈ S :=
iff.intro
  (suppose t ∈ complement '[S],
    obtain t' [(Ht' : t' ∈ S) (Ht : -t' = t)], from this,
    show -t ∈ S, by rewrite [-Ht, comp_comp]; exact Ht')
  (suppose -t ∈ S,
    have -(-t) ∈ complement '[S], from mem_image_of_mem complement this,
    show t ∈ complement '[S], from comp_comp t ▸ this)

theorem image_id {X : Type} (s : set X) : id '[s] = s :=
ext (take x, iff.intro
  (suppose x ∈ id '[s],
    obtain x' [(Hx' : x' ∈ s) (x'eq : x' = x)], from this,
    show x ∈ s, by rewrite [-x'eq]; apply Hx')
  (suppose x ∈ s, mem_image_of_mem id this))

theorem complement_compose_complement {X : Type} :
  #function complement ∘ complement = @id (set X) :=
funext (λ s, comp_comp s)

theorem complement_complement_image {X : Type} (S : set (set X)) :
  complement '[complement '[S]] = S :=
by rewrite [-image_compose, complement_compose_complement, image_id]

theorem comp_sUnion {X : Type} (S : set (set X)) :
  - ⋃₀ S = ⋂₀ (complement '[S]) :=
ext (take x, iff.intro
  (assume H : x ∈ -(⋃₀ S),
    take t, suppose t ∈ complement '[S],
    obtain t' [(Ht' : t' ∈ S) (Ht : -t' = t)], from this,
    have x ∈ -t', from suppose x ∈ t', H (mem_sUnion this Ht'),
    show x ∈ t, using this, by rewrite -Ht; apply this)
  (assume H : x ∈ ⋂₀ (complement '[S]),
    suppose x ∈ ⋃₀ S,
    obtain t [(tS : t ∈ S) (xt : x ∈ t)], from this,
    have -t ∈ complement '[S], from mem_image_of_mem complement tS,
    have x ∈ -t, from H this,
    show false, proof this xt qed))

theorem sUnion_eq_comp_sInter_comp {X : Type} (S : set (set X)) :
  ⋃₀ S = - ⋂₀ (complement '[S]) :=
by rewrite [-comp_comp, comp_sUnion]

theorem comp_sInter {X : Type} (S : set (set X)) :
  - ⋂₀ S = ⋃₀ (complement '[S]) :=
by rewrite [sUnion_eq_comp_sInter_comp, complement_complement_image]

theorem sInter_eq_comp_sUnion_comp {X : Type} (S : set (set X)) :
   ⋂₀ S = -(⋃₀ (complement '[S])) :=
by rewrite [-comp_comp, comp_sInter]

theorem comp_Union {X I : Type} (s : I → set X) : - (⋃ i, s i) = (⋂ i, - s i) :=
by rewrite [Union_eq_sUnion_image, comp_sUnion, -image_compose, -Inter_eq_sInter_image]

theorem Union_eq_comp_Inter_comp {X I : Type} (s : I → set X) : (⋃ i, s i) = - (⋂ i, - s i) :=
by rewrite [-comp_comp, comp_Union]

theorem comp_Inter {X I : Type} (s : I → set X) : -(⋂ i, s i) = (⋃ i, - s i) :=
by rewrite [Inter_eq_sInter_image, comp_sInter, -image_compose, -Union_eq_sUnion_image]

theorem Inter_eq_comp_Union_comp {X I : Type} (s : I → set X) : (⋂ i, s i) = - (⋃ i, -s i) :=
by rewrite [-comp_comp, comp_Inter]

/-
Notes:
o Let's try "Open s" and "closed s" instead of openset and closedset.
o When you declare a class, it is better to use
    structure foo [class]
  than
    attribute foo [class]
  afterwards. When you do the first, the argument for [S : foo] is marked for
  type class inference in every struture.
o If we do make topology a class (which makes sense), then it should always be
  inferred by class inference. We should always mark it [τ : topology X], and
  we should never have to infer to it explicitly. For example, we should say "Open s"
  instead of "s ∈ τ".
o Use the naming conventions:
    https://github.com/leanprover/lean/blob/master/doc/lean/library_style.org
  Especially before we have really good automation, it is crucial that it is easy
  to guess theorem names. So the destructor for a topology, ∅ ∈ opens, should be
  "empty_mem_opens", and the theorem "Open (A ∪ B)" should be "Open_union", etc.
o To avoid universe problems, we need to use sUnion to state the closure property for opens.
  It was not hard to derive the version for indexed unions from it.
o It is better to state the definition of a topology in terms of closure under binary
  intersections. That makes it easier to show that something is a topology. It was not hard
  derive the version for arbitrary finite intersetions from that.
o Note the definition of bin_ext below. It made the proof of Open_union much shorter.
o It is more convenient to use -s then univ \ s.
o In general, if you see useful facts that you think should be in the main part
  of the library, gather them at the top of the file (as I did here).
-/

/- topology starts here -/

structure topology [class] (X : Type) :=
  (opens : set (set X))
  (empty_mem_opens : ∅ ∈ opens)
  (univ_mem_opens : univ ∈ opens)
  (sUnion_mem_opens : ∀ {S : set (set X)}, S ⊆ opens → ⋃₀ S ∈ opens)
  (inter_mem_opens : ∀₀ s ∈ opens, ∀₀ t ∈ opens, s ∩ t ∈ opens)

namespace topology

variables {X : Type} [topology X]

/- open sets -/

definition Open (s : set X) : Prop := s ∈ opens X

theorem Open_empty : Open (∅ : set X) :=
empty_mem_opens X

theorem Open_univ : Open (univ : set X) :=
univ_mem_opens X

theorem Open_sUnion {S : set (set X)} (H : ∀₀ t ∈ S, Open t) : Open (⋃₀ S) :=
sUnion_mem_opens H

theorem Open_Union {I : Type} {s : I → set X} (H : ∀ i, Open (s i)) : Open (⋃ i, s i) :=
have ∀₀ t ∈ s '[univ], Open t,
  from take t, suppose t ∈ s '[univ],
    obtain i [univi (Hi : s i = t)], from this,
    show Open t, by rewrite -Hi; exact H i,
using this, by rewrite Union_eq_sUnion_image; apply Open_sUnion this

private definition bin_ext (s t : set X) (n : ℕ) : set X :=
nat.cases_on n s (λ m, t)

private lemma Union_bin_ext (s t : set X) : (⋃ i, bin_ext s t i) = s ∪ t :=
ext (take x, iff.intro
  (suppose x ∈ Union (bin_ext s t),
    obtain i (Hi : x ∈ (bin_ext s t) i), from this,
    by cases i; apply or.inl Hi; apply or.inr Hi)
  (suppose x ∈ s ∪ t,
    or.elim this
      (suppose x ∈ s, exists.intro 0 this)
      (suppose x ∈ t, exists.intro 1 this)))

theorem Open_union {s t : set X} (Hs : Open s) (Ht : Open t) : Open (s ∪ t) :=
have ∀ i, Open (bin_ext s t i), by intro i; cases i; exact Hs; exact Ht,
show Open (s ∪ t), using this, by rewrite -Union_bin_ext; exact Open_Union this

theorem Open_inter {s t : set X} (Hs : Open s) (Ht : Open t) : Open (s ∩ t) :=
inter_mem_opens X Hs Ht

theorem Open_sInter_of_finite {s : set (set X)} [fins : finite s] (H : ∀₀ t ∈ s, Open t) :
  Open (⋂₀ s) :=
begin
  induction fins with a s fins anins ih,
    {rewrite sInter_empty, exact Open_univ},
  rewrite sInter_insert,
  apply Open_inter,
    show Open a, from H (mem_insert a s),
  apply ih, intros t ts,
  show Open t, from H (mem_insert_of_mem a ts)
end

/- closed sets -/

definition closed [reducible] (s : set X) : Prop := Open (-s)

theorem closed_iff_Open_comp (s : set X) : closed s ↔ Open (-s) := !iff.refl

theorem Open_iff_closed_comp (s : set X) : Open s ↔ closed (-s) :=
by rewrite [closed_iff_Open_comp, comp_comp]

theorem closed_comp {s : set X} (H : Open s) : closed (-s) :=
by rewrite [-Open_iff_closed_comp]; apply H

theorem closed_empty : closed (∅ : set X) :=
by rewrite [↑closed, comp_empty]; exact Open_univ

theorem closed_univ : closed (univ : set X) :=
by rewrite [↑closed, comp_univ]; exact Open_empty

theorem closed_sInter {S : set (set X)} (H : ∀₀ t ∈ S, closed t) : closed (⋂₀ S) :=
begin
  rewrite [↑closed, comp_sInter],
  apply Open_sUnion,
  intro t,
  rewrite [mem_image_complement, Open_iff_closed_comp],
  apply H
end

theorem closed_Inter {I : Type} {s : I → set X} (H : ∀ i, closed (s i : set X)) :
  closed (⋂ i, s i) :=
by rewrite [↑closed, comp_Inter]; apply Open_Union; apply H

theorem closed_inter {s t : set X} (Hs : closed s) (Ht : closed t) : closed (s ∩ t) :=
by rewrite [↑closed, comp_inter]; apply Open_union; apply Hs; apply Ht

theorem closed_union {s t : set X} (Hs : closed s) (Ht : closed t) : closed (s ∪ t) :=
by rewrite [↑closed, comp_union]; apply Open_inter; apply Hs; apply Ht

theorem closed_sUnion_of_finite {s : set (set X)} [fins : finite s] (H : ∀₀ t ∈ s, closed t) :
  closed (⋂₀ s) :=
begin
  rewrite [↑closed, comp_sInter],
  apply Open_sUnion,
  intro t,
  rewrite [mem_image_complement, Open_iff_closed_comp],
  apply H
end

theorem open_diff {s t : set X} (Hs : Open s) (Ht : closed t) : Open (s \ t) :=
Open_inter Hs Ht

theorem closed_diff {s t : set X} (Hs : closed s) (Ht : Open t) : closed (s \ t) :=
closed_inter Hs (closed_comp Ht)

end topology

/- separation -/

structure T0_space [class] (X : Type) extends topology X :=
 (T0 : ∀ {x y}, x ≠ y → ∃ U, U ∈ opens ∧ ¬(x ∈ U ↔ y ∈ U))

namespace topology
  variables {X : Type} [T0_space X]

  theorem T0 {x y : X} (H : x ≠ y) : ∃ U, Open U ∧ ¬(x ∈ U ↔ y ∈ U) :=
  T0_space.T0 H
end topology

structure T1_space [class] (X : Type) extends topology X :=
  (T1 : ∀ {x y}, x ≠ y → ∃ U, U ∈ opens ∧ x ∈ U ∧ y ∉ U)

protected definition T0_space.of_T1 [reducible] [trans_instance] {X : Type} [T : T1_space X] :
  T0_space X :=
⦃T0_space, T,
  T0 := abstract
          take x y, assume H,
          obtain U [Uopens [xU ynU]], from T1_space.T1 H,
          exists.intro U (and.intro Uopens
            (show ¬ (x ∈ U ↔ y ∈ U), from assume H, ynU (iff.mp H xU)))
        end ⦄

namespace topology
  variables {X : Type} [T1_space X]

  theorem T1 {x y : X} (H : x ≠ y) : ∃ U, Open U ∧ x ∈ U ∧ y ∉ U :=
  T1_space.T1 H
end topology

structure T2_space [class] (X : Type) extends topology X :=
  (T2 : ∀ {x y}, x ≠ y → ∃ U V, U ∈ opens ∧ V ∈ opens ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅)

protected definition T1_space.of_T2 [reducible] [trans_instance] {X : Type} [T : T2_space X] :
  T1_space X :=
⦃T1_space, T,
  T1 := abstract
          take x y, assume H,
          obtain U [V [Uopens [Vopens [xU [yV UVempty]]]]], from T2_space.T2 H,
          exists.intro U (and.intro Uopens (and.intro xU
            (show y ∉ U, from assume yU,
              have y ∈ U ∩ V, from and.intro yU yV,
              show y ∈ ∅, from UVempty ▸ this)))
        end ⦄

namespace topology
  variables {X : Type} [T2_space X]

  theorem T2 {x y : X} (H : x ≠ y) : ∃ U V, Open U ∧ Open V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅ :=
  T2_space.T2 H
end topology

structure perfect_space [class] (X : Type) extends topology X :=
  (perfect : ∀ x, '{x} ∉ opens)

/- topology generated by a set -/

namespace topology

inductive opens_generated_by {X : Type} (B : set (set X)) : set X → Prop :=
| generators_mem : ∀ ⦃s : set X⦄, s ∈ B → opens_generated_by B s
| univ_mem       : opens_generated_by B univ
| inter_mem      : ∀ ⦃s t⦄, opens_generated_by B s → opens_generated_by B t →
                    opens_generated_by B (s ∩ t)
| sUnion_mem     : ∀ ⦃S : set (set X)⦄, S ⊆ opens_generated_by B → opens_generated_by B (⋃₀ S)

definition topology_generated_by [instance] [reducible] {X : Type} (B : set (set X)) : topology X :=
⦃topology,
  opens            := opens_generated_by B,
  empty_mem_opens  := abstract
                        have ∅ ⊆ opens_generated_by B, from empty_subset _,
                        have opens_generated_by B (⋃₀ ∅),
                          from opens_generated_by.sUnion_mem this,
                        show opens_generated_by B ∅,
                          using this, by rewrite -sUnion_empty; apply this
                      end,
  univ_mem_opens   := opens_generated_by.univ_mem B,
  sUnion_mem_opens := opens_generated_by.sUnion_mem,
  inter_mem_opens  := λ s Hs t Ht, opens_generated_by.inter_mem Hs Ht
⦄

theorem generators_mem_topology_generated_by {X : Type} (B : set (set X)) :
  let T := topology_generated_by B in
  ∀₀ s ∈ B, @Open _ T s :=
λ s H, opens_generated_by.generators_mem H

end topology

/- intervals -/

section
  variables {A : Type} [Astruc : order_pair A]
  include Astruc

  definition Ioo (a b : A) : set A := {x | a < x ∧ x < b}
  definition Ioc (a b : A) : set A := {x | a < x ∧ x ≤ b}
  definition Ico (a b : A) : set A := {x | a ≤ x ∧ x < b}
  definition Icc (a b : A) : set A := {x | a ≤ x ∧ x ≤ b}
  definition Iou (a : A)   : set A := {x | a < x}
  definition Icu (a : A)   : set A := {x | a ≤ x}
  definition Iuo (b : A)   : set A := {x | x < b}
  definition Iuc (b : A)   : set A := {x | x ≤ b}

  notation `'` `(` a `,` b `)`     := Ioo a b
  notation `'` `(` a `,` b `]`     := Ioc a b
  notation `'[` a `,` b `)`        := Ico a b
  notation `'[` a `,` b `]`        := Icc a b
  notation `'` `(` a `,` `∞` `)`   := Iou a
  notation `'[` a `,` `∞` `)`      := Icu a
  notation `'` `(` `-∞` `,` b `)`  := Iuo b
  notation `'` `(` `-∞` `,` b `]`  := Iuc b

  variables (a b c d e f : A)

  proposition Iou_inter_Iuo : '(a, ∞) ∩ '(-∞, b) = '(a, b) := rfl

end

/- Order Topology -/

namespace topology

attribute topology.opens [coercion]

variables {X : Type} [L : linear_strong_order_pair X] {B : set (set X)}

include L

notation `linorder_generators` := {y | ∃ a, y = '(a, ∞) } ∪ {y | ∃ a, y = '(-∞, a)}

definition linorder_topology [instance] : topology X := 
  topology_generated_by linorder_generators

theorem open_le {a : X} : Open '(a, ∞) := 
(generators_mem_topology_generated_by linorder_generators) (!mem_unionl (exists.intro a rfl))

theorem open_ge {a : X} : Open '(-∞, a) := 
(generators_mem_topology_generated_by linorder_generators) (!mem_unionr (exists.intro a rfl))

theorem closed_lt {a : X} : closed ('[a,∞)) := sorry

theorem closed_gt {a : X} : closed '(-∞,a] := sorry

theorem linorder_seperation {x y : X} :
  x < y → ∃ a, ∃ b, x < a ∧ b < y ∧ '(-∞, a) ∩ '(b, ∞) = ∅ := sorry
 
protected definition T2_space.of_linorder_topology [reducible] [trans_instance] :
  T2_space X :=
⦃ T2_space, linorder_topology,
  T2 := sorry ⦄

theorem open_right {S : set X} {x y : X} :
  (Open S ∧ x ∈ S ∧ x < y) → ∃ b, b > x ∧ '(-∞, b) ⊆ S := 
sorry

theorem open_left {S : set X} {x y : X} :
  (Open S ∧ x ∈ S ∧ y < x) → ∃ b, b < x ∧ '(b, ∞) ⊆ S :=
sorry

end topology
