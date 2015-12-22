import data.set data.nat
open algebra eq.ops set nat

variable {X : Type}

structure topology (X : Type) :=
  (top : set (set X))
  (empt : ∅ ∈ top)
  (subs : ∀ s, s ∈ top → s ⊆ @univ X)
  (entire : @univ X ∈ top)
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

theorem fin_inter_open {τ : topology X} (S : set (set X)) {fin : finite S} :
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

definition closedset [τ : topology X] (s : set X) : Prop := (@univ X) \ s ∈ τ

theorem space_closed {τ : topology X} :
  closedset (@univ X) := 
have (@univ X)\(@univ X) = ∅, from ext(
  take x,
  iff.intro
    (suppose x ∈ (@univ X)\(@univ X), !not.elim (and.elim_right this) (and.elim_left this))
    (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
show (@univ X)\(@univ X) ∈ τ, from this⁻¹ ▸ !topology.empt

theorem empty_closed (τ : topology X) : -- Can't write closedset ∅... type class inference can't find τ?
   (@univ X) \ ∅ ∈ τ := 
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

end 

theorem fin_inter_closed {τ : topology X} (S : set (set X)) {fin : finite S} :
  (∀ s, s ∈ S → closedset s) → closedset (sUnion S) := sorry

theorem cinter_closed (τ : topology X) (S : ℕ → set X) :
  (∀ i, closedset (S i)) → closedset (Inter S) := sorry

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

theorem closed_diff {τ : topology X} (A B : set X) (CloA : closedset A) (OpB : openset B) :
  openset (A \ B) := sorry

/- Kologorov, Frechet and Hausdorff spaces  -/

structure Kolmogorov_space [class] (X : Type) extends topology X :=
 (Kolmogorov : ∀ x y, x ≠ y → ∃ U, U ∈ top ∧ ¬(x ∈ U ↔ y ∈ U))

attribute Kolmogorov_space.top [coercion]

theorem seperation_Kolmogorov {K : Kolmogorov_space X} :
  ∀ x y, x ≠ y ↔ ∃ U, U ∈ K ∧ ¬(x ∈ U ↔ y ∈ U) := sorry

structure Frechet_space [class] (X : Type) extends topology X := 
  (Frechet : ∀ x y, x ≠ y → ∃ U, U ∈ top ∧ x ∈ U ∧ y ∉ U)

attribute Frechet_space.top [coercion]

theorem seperation_Frechet {F : Frechet_space X} :
  ∀ x y, x ≠ y ↔ ∃ U, U ∈ F ∧ x ∈ U ∧ y ∉ U := sorry

theorem closed_singleton {F : Frechet_space X} :
  ∀ a, (@univ X)\'{a} ∈ F := sorry 

theorem closed_insert {F : Frechet_space X} (S : set X):
  ∀ a, closedset S → closedset (insert a S) := sorry

structure Hausdorff_space [class] (X : Type) extends topology X :=
  (Hausdorff : ∀ x y, x ≠ y → ∃ U V, U ∈ top ∧ V ∈ top ∧ x ∈ U ∧ y ∈ V ∧ (U ∩ V = ∅))

attribute Hausdorff_space.top [coercion]

theorem seperation_Hausdorff {H : Hausdorff_space X} : 
  ∀ x y, x ≠ y ↔ ∃ U V, U ∈ H ∧ V ∈ H ∧ x ∈ U ∧ y ∈ V ∧ (U ∩ V = ∅) := sorry 

structure perfect_space [class] (X : Type) extends topology X :=
  (perfect : ∀ x, ¬('{x} ∈ top))

end top

/-  Do continuity next -/


