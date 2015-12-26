/-
Copyright (c) 2015 Jacob Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Gross

Open/Closed sets, seperation axioms and generator topologies
-/

import data.set data.nat data.real
open algebra eq.ops set nat real

variable {X : Type}

structure topology (X : Type) :=
  (top : set (set X))
  (empty : ∅ ∈ top)
  (univ : univ ∈ top)
  (union : ∀ I : Type.{1}, ∀ s : I → set X, (∀ i, s i ∈ top) → (Union s) ∈ top)
  (fin_inter : ∀ s, finite s → s ⊆ top → (sInter s ∈ top))

attribute topology [class]
attribute topology.top [coercion]

namespace top

definition openset [τ : topology X] (s : set X) : Prop := s ∈ τ

private definition bin_ext (A B : set X)  : ℕ → set X := 
  λ i, if i ≤ 1 then (if i = 0 then A else B) else ∅

theorem bin_union_open {τ : topology X} {A B : set X} (OpA : A ∈ τ) (OpB : B ∈ τ) :
  A ∪ B ∈ τ := 
have H : Union (bin_ext A B) = A ∪ B, from ext(
  take x,
  iff.intro
    (suppose x ∈ Union (bin_ext A B), 
      obtain i (Hi : x ∈ (bin_ext A B) i), from this,
      assert i ≤ 1, from not_not_elim
     (not.intro(
       suppose ¬(i ≤ 1),
       have (bin_ext A B) i = ∅, by rewrite[↑bin_ext, if_neg this],
       have x ∈ ∅, from this ▸ Hi,
       show false, from absurd this !not_mem_empty)),
      show x ∈ A ∪ B, from
        if Hp : i ≤ 1 then
          if Hpp : i = 0 then
           have (bin_ext A B) i = A, by rewrite[↑bin_ext, if_pos Hp, if_pos Hpp],
           have x ∈ A, from this ▸ Hi,
           show x ∈ A ∪ B, from !mem_union_left this
          else 
           have (bin_ext A B) i = B, by rewrite[↑bin_ext, if_pos Hp, if_neg Hpp],
           have x ∈ B, from this ▸ Hi,
           show x ∈ A ∪ B, from !mem_union_right this 
        else
         have (bin_ext A B) i = ∅, by rewrite[↑bin_ext, if_neg Hp],
         have x ∈ ∅, from this ▸ Hi,
         show x ∈ A ∪ B, from !not.elim !not_mem_empty this)
    (suppose x ∈ A ∪ B, 
     assert A ∪ B ⊆ Union (bin_ext A B), from
     take x,
     suppose x ∈ A ∪ B,
       or.elim 
         (mem_or_mem_of_mem_union `x ∈ A ∪ B`) 
         (suppose x ∈ A, exists.intro 0 this)
         (suppose x ∈ B, exists.intro 1 this),
    show x ∈ Union (bin_ext A B), from (!mem_of_subset_of_mem this) `x ∈ A ∪ B`)),
have ∀ i, (bin_ext A B) i ∈ τ, from 
   take i,
   if Hp : i ≤ 1 then
     if Hpp : i = 0 then
       by rewrite[↑bin_ext, if_pos Hp, if_pos Hpp]; exact OpA
     else
       by rewrite[↑bin_ext, if_pos Hp, if_neg Hpp]; exact OpB
     else 
       by rewrite[↑bin_ext, if_neg Hp]; exact !topology.empty,
have Union (bin_ext A B) ∈ τ, from !topology.union this,
show  A ∪ B ∈ τ, from H ▸ this

theorem fin_union_open {τ : topology X} (S : set (set X)) {fin : finite S} :
  (∀ s, s ∈ S → openset s) → openset (sUnion S) := 
!induction_on_finite
  (suppose ∀ s, s ∈ ∅ → openset s,
     have sUnion ∅ = ∅, from ext (λx, iff.intro
          (suppose x ∈ sUnion ∅,
            obtain c [(hc : c ∈ ∅) (xc : x ∈ c)], from this,
            show _, from !not.elim !not_mem_empty hc)
          (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
   show openset (sUnion ∅), from this⁻¹ ▸ !topology.empty)
  (begin
   intro a s fins,
   λ H₁, λ H₂, λ H₃,
   !sUnion_insert⁻¹ ▸ (!bin_union_open (H₃ a !mem_insert) (H₂(
     λ s, λ s', H₃ s (!mem_insert_of_mem s'))))
   end)

theorem bin_inter_open {τ : topology X} {A B : set X} (OpA : A ∈ τ) (OpB : B ∈ τ) :
  A ∩ B ∈ τ :=
have finite (∅ : set X), from !finite_empty,
have '{A} = insert A ∅, from ext(
  take x,
  iff.intro
    (assume xA, ((iff.elim_left !mem_singleton_iff) xA)⁻¹ ▸ !mem_insert)
    (suppose x ∈ insert A ∅, or.elim 
      (!eq_or_mem_of_mem_insert this)
      (suppose x = A, this⁻¹ ▸ !mem_singleton)
      (suppose x ∈ ∅, !not.elim !not_mem_empty this))),
have finite '{A}, from finite_insert A ∅,
have {x | x = A ∨ x = B} = insert B '{A}, from ext(
  take x,
  iff.intro
    (suppose x ∈ {x | x = A ∨ x = B}, or.elim this
        (suppose x = A, !mem_insert_of_mem (this⁻¹ ▸ !mem_singleton))
        (suppose x = B, this⁻¹ ▸ !mem_insert))
    (suppose x ∈ insert B '{A}, or.elim (!eq_or_mem_of_mem_insert this)
        (suppose x = B, or.inr this)
        (suppose x ∈ '{A}, or.inl ((iff.elim_left !mem_singleton_iff) this)))),
have finite {x | x = A ∨ x = B}, from this⁻¹ ▸ (finite_insert B '{A}),
have {x | x = A ∨ x = B} ⊆ τ, from
  take y,
  suppose y ∈ {x | x = A ∨ x = B},
  show y ∈ τ, from or.elim
    (this)
    (suppose y = A, this⁻¹ ▸ OpA)
    (suppose y = B, this⁻¹ ▸ OpB),
have H : sInter {x | x = A ∨ x = B} ∈ τ, from !topology.fin_inter `finite {x | x = A ∨ x = B}` this,
have A ∩ B = sInter {x | x = A ∨ x = B}, from ext(
  take x,
  iff.intro
    (suppose x ∈ A ∩ B, 
      take y,
      suppose y ∈ {x | x = A ∨ x = B}, 
      show x ∈ y, from or.elim
        (this)
        (suppose y = A,
          have x ∈ A, from and.elim_left `x ∈ A ∩ B`,
          show x ∈ y, from `y = A`⁻¹ ▸ this)
        (suppose y = B, 
          have x ∈ B, from and.elim_right `x ∈ A ∩ B`,
          show x ∈ y, from `y = B`⁻¹ ▸ this))
    (suppose x ∈ sInter {x | x = A ∨ x = B}, 
      have H : ∀ y, y ∈ {x | x = A ∨ x = B} → x ∈ y, from this,
      have x ∈ A, from (H A) (or.inl rfl),
      have x ∈ B, from (H B) (or.inr rfl),
      show x ∈ A ∩ B, from and.intro `x ∈ A` `x ∈ B`)),
show _, from this⁻¹ ▸ H

definition closedset [τ : topology X] (s : set X) : Prop := univ \ s ∈ τ

theorem space_closed {τ : topology X} :
  closedset (@univ X) := 
have univ\univ = ∅, from ext(
  take x,
  iff.intro
    (suppose x ∈ univ\univ, !not.elim (and.elim_right this) (and.elim_left this))
    (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
show univ\univ ∈ τ, from this⁻¹ ▸ !topology.empty

theorem empty_closed (τ : topology X) :
   univ \ ∅ ∈ τ := 
have univ \ ∅ = univ, from ext(
  take x,
  iff.intro
    (suppose x ∈ univ \ ∅, and.elim_left this)
    (suppose x ∈ univ, and.intro this !not_mem_empty)),
show _, from this⁻¹ ▸ !topology.univ

section

open classical

lemma diff_diff_univ (A : set X) :
  univ \ (univ \ A ) = A := 
ext(
  take x,
  iff.intro
    (suppose x ∈ univ \ (univ \ A ), 
      have ¬(x ∈ univ ∧ x ∉ A), from and.elim_right this,
      have ¬(x ∈ univ) ∨ ¬(x ∉ A), from (and.elim_left !not_and_iff_not_or_not) this,
      have ¬¬(x ∈ univ), from (and.elim_right not_not_iff) (and.elim_left `x ∈ (@univ X) \ ( (@univ X) \ A )`),
      have ¬(x ∉ A), from or_resolve_right `¬(x ∈ univ) ∨ ¬(x ∉ A)` this,
      show _, from not_not_elim this)
    (suppose x ∈ A, 
      have ¬¬(x ∈ A), from (and.elim_right !not_not_iff) this,
      have ¬(x ∈ univ) ∨ ¬¬(x ∈ A), from or.inr this,
      have ¬(x ∈ univ ∧ x ∉ A), from (and.elim_right !not_and_iff_not_or_not) this,
      show _, from and.intro !mem_univ this))

theorem bin_inter_closed {τ : topology X} (A B : set X) (CloA : closedset A) (CloB: closedset B) :
  closedset (A ∩ B) :=
 have H : closedset (univ \ (univ \ A ∪ univ \ B)), from
   begin
     rewrite[↑closedset, diff_diff_univ],
     exact !bin_union_open CloA CloB,
   end,
 have A ∩ B = univ \ (univ \ A ∪ univ \ B), from ext(
 take x,
 iff.intro
   (suppose x ∈ A ∩ B,
     have x ∈ univ, from !mem_univ,
     have x ∉ (univ \ A ∪ univ \ B), from not.intro(
       suppose x ∈ (univ \ A ∪ univ \ B),
       show false, from or.elim this
         (suppose x ∈ univ ∧ x ∉ A, absurd (and.elim_left `x ∈ A ∩ B`) (and.elim_right this))
         (suppose x ∈ univ ∧ x ∉ B, absurd (and.elim_right `x ∈ A ∩ B`) (and.elim_right this))),
     show _, from and.intro `x ∈ univ` this)
   (suppose x ∈ univ \ (univ \ A ∪ univ \ B),
     have H : x ∈ univ ∧ x ∉ (univ \ A ∪ univ \ B), from this,
     have ¬(x ∈ (univ \ A ∪ univ \ B)), from and.elim_right this,
     have H1 : ¬(x ∈ (univ \ A)) ∧ ¬(x ∈ (univ \ B)), from (iff.elim_left !not_or_iff_not_and_not this),
     have ¬(x ∈ univ ∧ x ∉ A), from and.elim_left H1,
     have ¬(x ∈ univ) ∨ ¬(x ∉ A), from (iff.elim_left !not_and_iff_not_or_not) this, 
     have ¬¬(x ∈ univ), from (iff.elim_right not_not_iff) (and.elim_left H),
     have x ∈ A, from not_not_elim (or_resolve_right `¬(x ∈ univ) ∨ ¬(x ∉ A)` this),
     have ¬(x ∈ univ ∧ x ∉ B), from and.elim_right H1,
     have ¬(x ∈ univ) ∨ ¬(x ∉ B), from (iff.elim_left !not_and_iff_not_or_not) this, 
     have x ∈ B, from not_not_elim (or_resolve_right this `¬¬(x ∈ univ)`),
     show _, from and.intro `x ∈ A` `x ∈ B`)),
 show _, from this⁻¹ ▸ H

theorem closed_diff {τ : topology X} (A B : set X) (CloA : closedset A) (OpB : openset B) :
  closedset (A \ B) :=
have H : A \ B = A ∩ (univ\B), from ext(
  take x,
  iff.intro
    (suppose x ∈ A \ B, and.intro (and.elim_left `x ∈ A \ B`) ( and.intro !mem_univ (and.elim_right this)))
    (suppose x ∈ A ∩ (univ\B), and.intro (and.elim_left this) (and.elim_right (and.elim_right this)))),
have closedset (univ\B), by rewrite[↑closedset]; exact (!diff_diff_univ⁻¹ ▸ OpB),
have closedset (A ∩ (univ\B)), from !bin_inter_closed CloA this,
show _, from H⁻¹ ▸ this

theorem cinter_closed (τ : topology X) (S : ℕ → set X) :
  (∀ i, closedset (S i)) → closedset (Inter S) := 
suppose ∀ i, closedset (S i),
have openset (Union (λ i, univ\(S i))), from !topology.union (take i, this i),
have H : openset (univ\(univ\(Union (λ i, univ\(S i))))), from !diff_diff_univ⁻¹ ▸ this,
have Inter S = univ\(Union (λ i, univ\(S i))), from ext(
  take x,
  iff.intro
    (suppose x ∈ Inter S,
      have x ∉ (Union (λ i, univ\(S i))), from not.intro(
        suppose x ∈ (Union (λ i, univ\(S i))),
        obtain i (Hi : x ∈ univ\(S i)), from this,
        have x ∉ S i, from and.elim_right Hi,
        have ∀ i, x ∈ S i, from `x ∈ Inter S`,
        absurd  (this i) `x ∉ S i`),
      show _, from and.intro !mem_univ this)
    (suppose x ∈ univ\(Union (λ i, univ\(S i))),
      have ¬ ∃ i, x ∈ univ\(S i), from and.elim_right this,
      have ∀ i, x ∉ (univ\(S i)), from iff.elim_left !forall_iff_not_exists this,
      have ∀ i, x ∈ S i, from 
        take i,
        have ¬(x ∈ univ ∧ x ∉ S i), from `∀ i, x ∉ (univ\(S i))` i,
        have x ∉ univ ∨ ¬(x ∉ S i), from iff.elim_left !not_and_iff_not_or_not this,
        or.elim
          this
          (suppose x ∉ univ, !not.elim this !mem_univ)
          (suppose ¬(x ∉ S i), not_not_elim this),
      show _, from this)),
show _, from this⁻¹ ▸ H

end 

theorem bin_union_closed {τ : topology X} (A B : set X) (CloA : closedset A) (CloB : closedset B) :
  closedset (A ∪ B) := 
have H : univ \ (A ∪ B) = (univ \ A) ∩ (univ \ B), from ext(
  take x,
  iff.intro
    (suppose x ∈ univ \ (A ∪ B),
      have ¬(x ∈ A ∨ x ∈ B), from and.elim_right this,
      have x ∉ A ∧ x ∉ B, from (and.elim_left !not_or_iff_not_and_not) this,
      have x ∈ (univ \ A), from and.intro !mem_univ (and.elim_left this),
      have x ∈ (univ \ B), from and.intro !mem_univ (and.elim_right `x ∉ A ∧ x ∉ B`),
      show _, from and.intro `x ∈ (univ \ A)` this)
    (suppose x ∈ (univ \ A) ∩ (univ \ B),
      have x ∉ A, from and.elim_right (and.elim_left this),
      have x ∉ B, from and.elim_right (and.elim_right `x ∈ (univ \ A) ∩ (univ \ B)`),
      have ¬(x ∈ A ∨ x ∈ B), from  (and.elim_right !not_or_iff_not_and_not) (and.intro `x ∉ A` this), 
      show _, from and.intro !mem_univ this)),
have openset ((univ \ A) ∩ (univ \ B)), from !bin_inter_open CloA CloB, 
show openset (univ \ (A ∪ B)), from H⁻¹ ▸ this

theorem fin_union_closed {τ : topology X} (S : set (set X)) {fin : finite S} :
  (∀ s, s ∈ S → closedset s) → closedset (sUnion S) := 
!induction_on_finite
  (suppose ∀ s, s ∈ ∅ → closedset s, 
        have sUnion ∅ = ∅, from ext (λx, iff.intro
          (suppose x ∈ sUnion ∅,
            obtain c [(hc : c ∈ ∅) (xc : x ∈ c)], from this,
            show _, from !not.elim !not_mem_empty hc)
          (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
   show closedset (sUnion ∅), from this⁻¹ ▸ !empty_closed)
  (begin
    intro a s fins,
    λ H₁, λ H₂, λ H₃,
    !sUnion_insert⁻¹ ▸ (!bin_union_closed (H₃ a !mem_insert) (H₂(
      λ s, λ s', H₃ s (!mem_insert_of_mem s'))))
   end)

theorem fin_inter_closed {τ : topology X} (S : set (set X)) {fin : finite S} :
  (∀ s, s ∈ S → closedset s) → closedset (sInter S) := 
!induction_on_finite
  (suppose ∀ s, s ∈ ∅ → closedset s,
   have sInter ∅ = univ, from ext(
     take x,
     iff.intro
       (suppose x ∈ sInter ∅, !mem_univ)
       (suppose x ∈ univ, 
           take c,
           suppose c ∈ ∅,
           !not.elim !not_mem_empty this)),
   show closedset (sInter ∅), from this⁻¹ ▸ !space_closed)
  (begin
    intro a s fins,
    λ H₁, λ H₂, λ H₃,
    !sInter_insert⁻¹ ▸ (!bin_inter_closed (H₃ a !mem_insert) (H₂(
      λ s, λ s', H₃ s (!mem_insert_of_mem s'))))
   end)

theorem open_diff {τ : topology X} (A B : set X) (OpA : openset A) (CloB : closedset B) :
  openset (A \ B) := 
have H : A \ B = A ∩ (univ\B), from ext(
  take x,
  iff.intro
    (suppose x ∈ A \ B, and.intro (and.elim_left `x ∈ A \ B`) ( and.intro !mem_univ (and.elim_right this)))
    (suppose x ∈ A ∩ (univ\B), and.intro (and.elim_left this) (and.elim_right (and.elim_right this)))),
have openset (univ\B), from CloB,
have openset (A ∩ (univ\B)), from !bin_inter_open OpA this,
show _, from H⁻¹ ▸ this

/- Seperation  -/

structure T0_space [class] (X : Type) extends topology X :=
 (T0 : ∀ x y, x ≠ y → ∃ U, U ∈ top ∧ ¬(x ∈ U ↔ y ∈ U))

attribute T0_space.top [coercion]

theorem seperation_T0 {τ : T0_space X} :
  ∀ x y, x ≠ y ↔ ∃ U, U ∈ τ ∧ ¬(x ∈ U ↔ y ∈ U) := 
take x y,
iff.intro
  (suppose x ≠ y, T0_space.T0 x y this)
  (suppose ∃ U, U ∈ τ ∧ ¬(x ∈ U ↔ y ∈ U),
    obtain U (HU:  U ∈ τ ∧ ¬(x ∈ U ↔ y ∈ U)), from this,
    not.intro(
      suppose x = y,
      have x ∈ U ↔ y ∈ U, from iff.intro (λ H, `x = y` ▸ H) (λ H, `x = y`⁻¹ ▸ H),
      show false, from absurd this (and.elim_right HU)))

structure T1_space [class] (X : Type) extends topology X := 
  (T1 : ∀ x y, x ≠ y → ∃ U, U ∈ top ∧ x ∈ U ∧ y ∉ U)

attribute T1_space.top [coercion]

theorem seperation_T1 {τ : T1_space X} :
  ∀ x y, x ≠ y ↔ ∃ U, U ∈ τ ∧ x ∈ U ∧ y ∉ U := 
take x y,
iff.intro
  (suppose x ≠ y, T1_space.T1 x y this)
  (suppose ∃ U, U ∈ τ ∧ x ∈ U ∧ y ∉ U, 
    obtain U (HU : U ∈ τ ∧ x ∈ U ∧ y ∉ U), from this,
    not.intro(
      suppose x = y, 
      have x ∉ U, from this⁻¹ ▸ (and.elim_right (and.elim_right HU)),
      show false, from absurd (and.elim_left (and.elim_right HU)) this))

lemma T1_implies_T0 {τ : T1_space X} : 
  ∀ x y, x ≠ y → ∃ U, U ∈ τ ∧ ¬(x ∈ U ↔ y ∈ U) := 
take x y,
suppose x ≠ y,
obtain U (HU : U ∈ τ ∧ x ∈ U ∧ y ∉ U), from !T1_space.T1 this,
have ¬(x ∈ U ↔ y ∈ U), from not.intro(
  suppose x ∈ U ↔ y ∈ U,
  have ¬(x ∈ U → y ∈ U), from not.intro(
    suppose x ∈ U → y ∈ U,
    have y ∈ U, from this (and.elim_left (and.elim_right HU)),
    have y ∉ U, from and.elim_right (and.elim_right HU),
    absurd `y ∈ U` this),
  absurd (iff.elim_left `x ∈ U ↔ y ∈ U`) this),
have U ∈ τ ∧ ¬(x ∈ U ↔ y ∈ U), from and.intro (and.elim_left HU) this,
show _, from exists.intro U this

definition T1_space.to_T0_space [trans_instance] [reducible] [τ : T1_space X] :
T0_space X :=
⦃ T0_space, 
  top       := T1_space.top X,
  empty      := T1_space.empty X,
  univ    := T1_space.univ X,
  union     := T1_space.union,
  fin_inter := T1_space.fin_inter,
  T0        := T1_implies_T0 ⦄

structure T2_space [class] (X : Type) extends topology X :=
  (T2 : ∀ x y, x ≠ y → ∃ U V, U ∈ top ∧ V ∈ top ∧ x ∈ U ∧ y ∈ V ∧ (U ∩ V = ∅))

attribute T2_space.top [coercion]

theorem seperation_T2 {τ : T2_space X} : 
  ∀ x y, x ≠ y ↔ ∃ U V, U ∈ τ ∧ V ∈ τ ∧ x ∈ U ∧ y ∈ V ∧ (U ∩ V = ∅) := 
take x y,
iff.intro
  (suppose x ≠ y, T2_space.T2 x y this)
  (suppose ∃ U V, U ∈ τ ∧ V ∈ τ ∧ x ∈ U ∧ y ∈ V ∧ (U ∩ V = ∅), 
    obtain U V (HUV : U ∈ τ ∧ V ∈ τ ∧ x ∈ U ∧ y ∈ V ∧ (U ∩ V = ∅)), from this,
    have U ∩ V = ∅, from and.elim_right (and.elim_right (and.elim_right (and.elim_right HUV))),
    have x ∈ U, from and.elim_left (and.elim_right (and.elim_right HUV)),
    have y ∈ V, from and.elim_left (and.elim_right (and.elim_right (and.elim_right HUV))),
    show x ≠ y, from
      not.intro(
        suppose x = y,
        have x ∈ V, from this⁻¹ ▸ `y ∈ V`,
        have x ∈ U ∩ V, from and.intro `x ∈ U` this,
        have x ∈ ∅, from `U ∩ V = ∅` ▸ this,
        absurd this !not_mem_empty))

lemma T2_implies_T1 {τ : T2_space X} : 
  ∀ x y, x ≠ y → ∃ U, U ∈ τ ∧ x ∈ U ∧ y ∉ U := 
take x y,
suppose x ≠ y,
obtain U V (HUV : U ∈ τ ∧ V ∈ τ ∧ x ∈ U ∧ y ∈ V ∧ (U ∩ V = ∅)), from !T2_space.T2 this,
have y ∉ U, from not.intro(
 suppose y ∈ U,
 have y ∈ V, from and.elim_left (and.elim_right (and.elim_right (and.elim_right HUV))),
 have y ∈ U ∩ V, from and.intro `y ∈ U` this,
 have y ∈ ∅, from (and.elim_right (and.elim_right (and.elim_right (and.elim_right HUV)))) ▸ this,
 absurd this !not_mem_empty),
have U ∈ τ ∧ x ∈ U ∧ y ∉ U, from and.intro (and.elim_left HUV) (and.intro (and.elim_left (and.elim_right (and.elim_right HUV))) this),
show _, from exists.intro U this

definition T2_space.to_T1_space [trans_instance] [reducible] [τ : T2_space X] :
T1_space X :=
⦃ T1_space, 
  top       := T2_space.top X,
  empty     := T2_space.empty X,
  univ      := T2_space.univ X,
  union     := T2_space.union,
  fin_inter := T2_space.fin_inter,
  T1        := T2_implies_T1 ⦄

structure perfect_space [class] (X : Type) extends topology X :=
  (perfect : ∀ x, ¬('{x} ∈ top))

/- Generators for Topologies -/

inductive generate_topology (B : set (set X))  : (X → Prop) → Prop :=
| UNIV : (generate_topology B) (λ x, true) 
| EMPTY : (generate_topology B) (λ x, false)
| Int :  ∀ a b, generate_topology B a → generate_topology B b → (generate_topology B (a ∩ b))
| UN : ∀ I : Type.{1}, ∀ U : I → set X, (∀ i, U i ∈ generate_topology B) → generate_topology B (Union U)
| Basis : ∀ s, B s → generate_topology B s

lemma generate_topology_Union (A : Type) (B : set (set A)) : 
  ∀ I : Type.{1}, ∀ U : I → set A, (∀ i, U i ∈ generate_topology B) → Union U ∈ generate_topology B := 
take I,
take U : I → set A,
suppose ∀ i, U i ∈ generate_topology B,
!generate_topology.UN this

open classical

private lemma fin_inter_ind_step (B : set (set X)) (a : set X) : 
  ∀ s, a ∉ s → (finite s → s ⊆ (generate_topology B) →  (sInter s ∈ (generate_topology B))) → 
(finite (insert a s) → (insert a s) ⊆ generate_topology B →  (sInter (insert a s) ∈ generate_topology B)) := 
take s,
λ H₁, λ H₂, λ H₃, λ H₄,
!sInter_insert⁻¹ ▸ (!generate_topology.Int ((H₄ a) !mem_insert)(H₂ (!finite_of_finite_insert H₃) (subset.trans (subset_insert a s) H₄)))

lemma generate_topology_fin_Inter {B : set (set X)} :
  ∀ s, finite s → s ⊆ (generate_topology B) → (sInter s ∈ (generate_topology B)) := 
take s,
if fin : finite s then 
  !induction_on_finite
    (suppose finite ∅,
     suppose ∅ ⊆ (generate_topology B),
     have (sInter (∅ : set (set X))) = univ, from ext(
     take x,
     iff.intro
       (suppose x ∈ sInter ∅, !mem_univ)
       (suppose x ∈ univ, 
           take c,
           suppose c ∈ ∅,
           !not.elim !not_mem_empty this)),
     have univ ∈ (generate_topology B), from generate_topology.UNIV B,
     show sInter ∅ ∈ (generate_topology B), from `sInter ∅ = univ`⁻¹ ▸ this)
    (begin
      intro a s fins,
      apply !fin_inter_ind_step
     end)
else 
  suppose finite s,
  suppose s ⊆ (generate_topology B),
  show sInter s ∈ (generate_topology B), from !not.elim fin `finite s`

definition generate_topology.to_topology [trans_instance] [reducible] (B : set (set X)) :
  topology X :=
⦃ topology, 
  top        := generate_topology B,
  empty      := generate_topology.EMPTY B,
  univ       := generate_topology.UNIV B,
  union      := generate_topology_Union X B,
  fin_inter  := generate_topology_fin_Inter ⦄

lemma basis_in_topology {B : set (set X)} : B ⊆ (generate_topology.to_topology B) := 
take s, 
suppose s ∈ B,
have s ∈ generate_topology B → s ∈ generate_topology.to_topology B, from 
  suppose s ∈ generate_topology B,
  have generate_topology B = topology.top (generate_topology.to_topology B), by rewrite[↑generate_topology.to_topology],
  show _, from this ▸ (generate_topology.Basis s `s ∈ B`),
show _, from this (generate_topology.Basis s `s ∈ B`)

end top

/- Linear Order Topologies  -- Move to a different file? -/

namespace order_topology

open top

section

  variable [L : linear_strong_order_pair X]
  include L

  definition linorder_topology : topology X :=
    generate_topology.to_topology ({y | ∃ a, y = {x | a < x} } ∪ {y | ∃ a, y = {x | a > x}})

  theorem open_lt {a : X} : {x | a < x} ∈ linorder_topology := 
    !basis_in_topology (!mem_unionl (exists.intro a rfl))

  theorem open_gt {a : X} : {x | a > x} ∈ linorder_topology := 
     !basis_in_topology (!mem_unionr (exists.intro a rfl))

  theorem closed_le {a : X} : univ \ {x | a ≤ x} ∈ linorder_topology := 
    have univ \ {x | a ≤ x} = {x | a > x}, from ext(
      take y,
      iff.intro
        (suppose y ∈ univ \ {x | a ≤ x}, lt_of_not_ge (and.elim_right this))
        (suppose y ∈ {x | a > x}, 
          have a > y, from this,
          have ¬ a ≤ y, from not.intro(
            suppose a ≤ y,
            have a < y ∨ a = y, from (iff.elim_left le_iff_lt_or_eq) this,
            have a < y → false, from assume H, absurd H (lt.asymm `a > y`),
            have a = y → false, from assume H, absurd H (ne_of_gt `a > y`),
            or.elim `a < y ∨ a = y` `a < y → false` `a = y → false`),
          and.intro !mem_univ this)),
    this⁻¹ ▸ !open_gt

  theorem closed_ge {a : X} : univ \ {x | a ≥ x} ∈ linorder_topology := 
    have univ \ {x | a ≥ x} = {x | a < x}, from ext(
      take y,
      iff.intro
        (suppose y ∈ univ \ {x | a ≥ x}, lt_of_not_ge (and.elim_right this))
        (suppose y ∈ {x | a < x},
          have a < y, from this,
          have ¬ a ≥ y, from not.intro(
            suppose a ≥ y,
            have a > y ∨ y = a, from (iff.elim_left le_iff_lt_or_eq) this,
            have a > y → false, from assume H, absurd H (lt.asymm `a < y`),
            have y = a → false, from assume H, absurd H (ne_of_gt `a < y`),
            or.elim `a > y ∨ y = a` `a > y → false` `y = a → false`),
          and.intro !mem_univ this)), 
    this⁻¹ ▸ open_lt

section

  open classical

  theorem seperation_linorder {x y : X} : 
    x < y → ∃ a, ∃ b, x < a ∧ b < y ∧ {x | x < a} ∩ {x | b < x} = ∅ :=
    suppose x < y,
    if ∃ z, x < z ∧ z < y then
      sorry 
    else 
      sorry

end

  definition linorder_topology.to_T2_space [trans_instance] [reducible] :
    T2_space X :=
  ⦃ T2_space, 
  top       := topology.top linorder_topology,
  empty     := topology.empty linorder_topology,
  univ      := topology.univ linorder_topology,
  union     := topology.union linorder_topology,
  fin_inter := topology.fin_inter linorder_topology,
  T2        := sorry ⦄

  theorem open_right {S : set X} {x y : X} :
    (S ∈ linorder_topology ∧ x ∈ S ∧ x < y) → ∃ b, b > x ∧ {x | x < b} ⊆ S := 
  sorry

  theorem open_left {S : set X} {x y : X} :
    (S ∈ linorder_topology ∧ x ∈ S ∧ y < x) → ∃ b, b < x ∧ {x | x > b} ⊆ S :=
  sorry

end

end order_topology


