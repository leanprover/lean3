import data.set data.nat
open algebra eq.ops set nat

variable {X : Type}

structure topology (X : Type) :=
  (top : set (set X))
  (empt : ∅ ∈ top)
  (subs : ∀ s, s ∈ top → s ⊆ univ)
  (entire : univ ∈ top)
  (union : ∀ s : ℕ → set X, (∀ i, s i ∈ top) → (Union s) ∈ top)
  (fin_inter : ∀ s, s ⊆ top → (sInter s ∈ top))

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
have ∀ i, openset ((bin_ext A B) i), from 
   take i,
   if Hp : i ≤ 1 then
     if Hpp : i = 0 then
       by rewrite[↑bin_ext, if_pos Hp, if_pos Hpp]; exact OpA
     else
       by rewrite[↑bin_ext, if_pos Hp, if_neg Hpp]; exact OpB
     else 
       by rewrite[↑bin_ext, if_neg Hp]; exact !topology.empt,
have Union (bin_ext A B) ∈ τ, from !topology.union this,
show  A ∪ B ∈ τ, from H ▸ this

theorem bin_inter_open {τ : topology X} {A B : set X} (OpA : A ∈ τ) (OpB : B ∈ τ) :
  A ∩ B ∈ τ :=
have {x | x = A ∨ x = B} ⊆ τ, from
  take y,
  suppose y ∈ {x | x = A ∨ x = B},
  show y ∈ τ, from or.elim
    (this)
    (suppose y = A, this⁻¹ ▸ OpA)
    (suppose y = B, this⁻¹ ▸ OpB),
have H : sInter {x | x = A ∨ x = B} ∈ τ, from !topology.fin_inter this,
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

theorem fin_union_open {τ : topology X} (S : set (set X)) {fin : finite S} :
  (∀ s, s ∈ S → openset s) → openset (sUnion S) := 
!induction_on_finite
  (suppose ∀ s, s ∈ ∅ → openset s,
     have sUnion ∅ = ∅, from ext (λx, iff.intro
          (suppose x ∈ sUnion ∅,
            obtain c [(hc : c ∈ ∅) (xc : x ∈ c)], from this,
            show _, from !not.elim !not_mem_empty hc)
          (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
   show openset (sUnion ∅), from this⁻¹ ▸ !topology.empt)
  (begin
   intro a s fins,
   λ H₁, λ H₂, λ H₃,
   !sUnion_insert⁻¹ ▸ (!bin_union_open (H₃ a !mem_insert) (H₂(
     λ s, λ s', H₃ s (!mem_insert_of_mem s'))))
   end)

definition closedset [τ : topology X] (s : set X) : Prop := univ \ s ∈ τ

theorem space_closed {τ : topology X} :
  closedset (@univ X) := 
have univ\univ = ∅, from ext(
  take x,
  iff.intro
    (suppose x ∈ univ\univ, !not.elim (and.elim_right this) (and.elim_left this))
    (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
show univ\univ ∈ τ, from this⁻¹ ▸ !topology.empt

theorem empty_closed (τ : topology X) : -- Can't write closedset ∅... type class inference can't find τ?
   univ \ ∅ ∈ τ := 
have (@univ X) \ ∅ = @univ X, from ext(
  take x,
  iff.intro
    (suppose x ∈ (@univ X) \ ∅, and.elim_left this)
    (suppose x ∈ @univ X, and.intro this !not_mem_empty)),
show _, from this⁻¹ ▸ !topology.entire

theorem bin_union_closed {τ : topology X} (A B : set X) (CloA : closedset A) (CloB : closedset B) :
  closedset (A ∪ B) := 
have H : (@univ X) \ (A ∪ B) = ((@univ X) \ A) ∩ ((@univ X) \ B), from ext(
  take x,
  iff.intro
    (suppose x ∈ (@univ X) \ (A ∪ B),
      have ¬(x ∈ A ∨ x ∈ B), from and.elim_right this,
      have x ∉ A ∧ x ∉ B, from (and.elim_left !not_or_iff_not_and_not) this,
      have x ∈ ((@univ X) \ A), from and.intro !mem_univ (and.elim_left this),
      have x ∈ ((@univ X) \ B), from and.intro !mem_univ (and.elim_right `x ∉ A ∧ x ∉ B`),
      show _, from and.intro `x ∈ ((@univ X) \ A)` this)
    (suppose x ∈ ((@univ X) \ A) ∩ ((@univ X) \ B),
      have x ∉ A, from and.elim_right (and.elim_left this),
      have x ∉ B, from and.elim_right (and.elim_right `x ∈ ((@univ X) \ A) ∩ ((@univ X) \ B)`),
      have ¬(x ∈ A ∨ x ∈ B), from  (and.elim_right !not_or_iff_not_and_not) (and.intro `x ∉ A` this), 
      show _, from and.intro !mem_univ this)),
have openset (((@univ X) \ A) ∩ ((@univ X) \ B)), from !bin_inter_open CloA CloB, 
show openset ((@univ X) \ (A ∪ B)), from H⁻¹ ▸ this

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

section

open classical

lemma diff_diff_univ (A : set X) :
  (@univ X) \ ((@univ X) \ A ) = A := 
ext(
  take x,
  iff.intro
    (suppose x ∈ (@univ X) \ ( (@univ X) \ A ), 
      have ¬(x ∈ (@univ X) ∧ x ∉ A), from and.elim_right this,
      have ¬(x ∈ (@univ X)) ∨ ¬(x ∉ A), from (and.elim_left !not_and_iff_not_or_not) this,
      have ¬¬(x ∈ (@univ X)), from (and.elim_right not_not_iff) (and.elim_left `x ∈ (@univ X) \ ( (@univ X) \ A )`),
      have ¬(x ∉ A), from or_resolve_right `¬(x ∈ (@univ X)) ∨ ¬(x ∉ A)` this,
      show _, from not_not_elim this)
    (suppose x ∈ A, 
      have ¬¬(x ∈ A), from (and.elim_right !not_not_iff) this,
      have ¬(x ∈ (@univ X)) ∨ ¬¬(x ∈ A), from or.inr this,
      have ¬(x ∈ (@univ X) ∧ x ∉ A), from (and.elim_right !not_and_iff_not_or_not) this,
      show _, from and.intro !mem_univ this))

theorem bin_inter_closed {τ : topology X} (A B : set X) (CloA : closedset A) (CloB: closedset B) :
  closedset (A ∩ B) :=
 have H : closedset ((@univ X)\((@univ X)\A ∪ (@univ X) \ B)), from
   begin
     rewrite[↑closedset, diff_diff_univ],
     exact !bin_union_open CloA CloB,
   end,
 have A ∩ B = (@univ X) \ ((@univ X) \ A ∪ (@univ X) \ B), from ext(
 take x,
 iff.intro
   (suppose x ∈ A ∩ B,
     have x ∈ @univ X, from !mem_univ,
     have x ∉ ((@univ X) \ A ∪ (@univ X) \ B), from not.intro(
       suppose x ∈ ((@univ X) \ A ∪ (@univ X) \ B),
       show false, from or.elim this
         (suppose x ∈ @univ X ∧ x ∉ A, absurd (and.elim_left `x ∈ A ∩ B`) (and.elim_right this))
         (suppose x ∈ @univ X ∧ x ∉ B, absurd (and.elim_right `x ∈ A ∩ B`) (and.elim_right this))),
     show _, from and.intro `x ∈ @univ X` this)
   (suppose x ∈ (@univ X)\((@univ X) \ A ∪ (@univ X) \ B),
     have H : x ∈ @univ X ∧ x ∉ ((@univ X) \ A ∪ (@univ X) \ B), from this,
     have ¬(x ∈ ((@univ X) \ A ∪ (@univ X) \ B)), from and.elim_right this,
     have H1 : ¬(x ∈ ((@univ X) \ A)) ∧ ¬(x ∈ ((@univ X) \ B)), from (iff.elim_left !not_or_iff_not_and_not this),
     have ¬(x ∈ (@univ X) ∧ x ∉ A), from and.elim_left H1,
     have ¬(x ∈ (@univ X)) ∨ ¬(x ∉ A), from (iff.elim_left !not_and_iff_not_or_not) this, 
     have ¬¬(x ∈ @univ X), from (iff.elim_right not_not_iff) (and.elim_left H),
     have x ∈ A, from not_not_elim (or_resolve_right `¬(x ∈ (@univ X)) ∨ ¬(x ∉ A)` this),
     have ¬(x ∈ (@univ X) ∧ x ∉ B), from and.elim_right H1,
     have ¬(x ∈ (@univ X)) ∨ ¬(x ∉ B), from (iff.elim_left !not_and_iff_not_or_not) this, 
     have x ∈ B, from not_not_elim (or_resolve_right this `¬¬(x ∈ (@univ X))`),
     show _, from and.intro `x ∈ A` `x ∈ B`)),
 show _, from this⁻¹ ▸ H

theorem closed_diff {τ : topology X} (A B : set X) (CloA : closedset A) (OpB : openset B) :
  closedset (A \ B) :=
have H : A \ B = A ∩ ((@univ X)\B), from ext(
  take x,
  iff.intro
    (suppose x ∈ A \ B, and.intro (and.elim_left `x ∈ A \ B`) ( and.intro !mem_univ (and.elim_right this)))
    (suppose x ∈ A ∩ ((@univ X)\B), and.intro (and.elim_left this) (and.elim_right (and.elim_right this)))),
have closedset ((@univ X)\B), by rewrite[↑closedset]; exact (!diff_diff_univ⁻¹ ▸ OpB),
have closedset (A ∩ ((@univ X)\B)), from !bin_inter_closed CloA this,
show _, from H⁻¹ ▸ this

theorem cinter_closed (τ : topology X) (S : ℕ → set X) :
  (∀ i, closedset (S i)) → closedset (Inter S) := 
suppose ∀ i, closedset (S i),
have ∀ i, openset (univ\(S i)), from take i, this i,
have openset (Union (λ i, univ\(S i))), from sorry,
have H : closedset (univ\(Union (λ i, univ\(S i)))), from sorry,
have Inter S = univ\(Union (λ i, univ\(S i))), from ext(
  take x,
  iff.intro
    (suppose x ∈ Inter S, sorry)
    (suppose x ∈ univ\(Union (λ i, univ\(S i))), sorry)),
show _, from this⁻¹ ▸ H

end 

theorem fin_inter_closed {τ : topology X} (S : set (set X)) {fin : finite S} :
  (∀ s, s ∈ S → closedset s) → closedset (sInter S) := 
!induction_on_finite
  (suppose ∀ s, s ∈ ∅ → closedset s,
   have sInter ∅ = @univ X, from ext(
     take x,
     iff.intro
       (suppose x ∈ sInter ∅, !mem_univ)
       (suppose x ∈ @univ X, 
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
have H : A \ B = A ∩ ((@univ X)\B), from ext(
  take x,
  iff.intro
    (suppose x ∈ A \ B, and.intro (and.elim_left `x ∈ A \ B`) ( and.intro !mem_univ (and.elim_right this)))
    (suppose x ∈ A ∩ ((@univ X)\B), and.intro (and.elim_left this) (and.elim_right (and.elim_right this)))),
have openset ((@univ X)\B), from CloB,
have openset (A ∩ ((@univ X)\B)), from !bin_inter_open OpA this,
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
  empt      := T1_space.empt X,
  subs      := T1_space.subs,
  entire    := T1_space.entire X,
  union     := T1_space.union,
  fin_inter := T1_space.fin_inter,
  T0        := T1_implies_T0 ⦄

theorem closed_singleton {τ : T1_space X} :
  ∀ a, (@univ X) \ '{a} ∈ τ := 
take a,
have H : openset (sUnion {s | openset s ∧ a ∉ s}), from sorry,
have univ \ '{a} = sUnion {s | openset s ∧ a ∉ s}, from sorry,
show _, from this⁻¹ ▸ H 

theorem closed_insert {τ : T1_space X} (S : set X):
  ∀ a, closedset S → closedset (insert a S) := 
take a,
suppose closedset S,
have H : insert a S = '{a} ∪ S, from sorry,
have closedset '{a}, from !closed_singleton,
have closedset ('{a} ∪ S), from !bin_union_closed this `closedset S`,
show closedset (insert a S), from H⁻¹ ▸ this

structure T2_space [class] (X : Type) extends topology X :=
  (T2 : ∀ x y, x ≠ y → ∃ U V, U ∈ top ∧ V ∈ top ∧ x ∈ U ∧ y ∈ V ∧ (U ∩ V = ∅))

attribute T2_space.top [coercion]

lemma T2_implies_T1 {τ : T2_space X} : 
  ∀ x y, x ≠ y → ∃ U, U ∈ τ ∧ x ∈ U ∧ y ∉ U := sorry

definition T2_space.to_T1_space [trans_instance] [reducible] [τ : T2_space X] :
T1_space X :=
⦃ T1_space, 
  top       := T2_space.top X,
  empt      := T2_space.empt X,
  subs      := T2_space.subs,
  entire    := T2_space.entire X,
  union     := T2_space.union,
  fin_inter := T2_space.fin_inter,
  T1        := T2_implies_T1 ⦄

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

structure perfect_space [class] (X : Type) extends topology X :=
  (perfect : ∀ x, ¬('{x} ∈ top))

end top


