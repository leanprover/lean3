import data.set data.nat
open algebra eq.ops set nat

variable {X : Type}

structure topology (X : Type) :=
  (space : set X)
  (top : set (set X))
  (empt : ∅ ∈ top)
  (entire : space ∈ top)
  (union : ∀ s : ℕ → set X, (∀ i, s i ∈ top) → (Union s) ∈ top)
  (fin_inter : ∀ s, s ⊆ top → (sInter s ∈ top))

attribute topology [class]
attribute topology.top [coercion]
attribute topology.space [coercion]

local abbreviation space := @topology.space 

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

theorem bin_inter_open {τ : topology X} (A B : set X) (OpA : A ∈ τ) (OpB : B ∈ τ) 
  : A ∩ B ∈ τ :=
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

definition closedset [τ : topology X] (s : set X) : Prop := (space τ)\s ∈ τ

theorem space_closed {τ : topology X} :
  closedset (space τ) := 
have (space τ)\(space τ) = ∅, from ext(
  take x,
  iff.intro
    (suppose x ∈ (space τ)\(space τ), !not.elim (and.elim_right this) (and.elim_left this))
    (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
show (space τ)\(space τ) ∈ τ, from this⁻¹ ▸ !topology.empt

theorem empty_closed (τ : topology X) : -- Can't write closedset ∅... type class inference can't find τ?
   (space τ)\∅ ∈ τ := 
have (space τ)\∅ = space τ, from ext(
  take x,
  iff.intro
    (suppose x ∈ (space τ)\∅, sorry)
    (suppose x ∈ space τ, sorry)),
show _, from this⁻¹ ▸ !topology.entire

theorem bin_union_closed {τ : topology X} (A B : set X) (CloA : closedset A) (CloB : closedset B) :
  closedset (A ∪ B) := sorry

theorem fin_union_closed {τ : topology X} (S : set (set X)) {fin : finite S} :
  (∀ s, s ∈ S → closedset s) → closedset (sUnion S) := sorry

theorem bin_inter_closed {τ : topology X} (A B : set X) (CloA : closedset A) (CloB: closedset B) :
  closedset (A ∩ B) := sorry

theorem fin_inter_closed {τ : topology X} (S : set (set X)) {fin : finite S} :
  (∀ s, s ∈ S → closedset s) → closedset (sUnion S) := sorry

theorem cinter_closed (τ : topology X) (S : ℕ → set X) :
  (∀ i, closedset (S i)) → closedset (Inter S) := sorry

definition clopen [τ : topology X] (s : set X) : Prop := openset s ∧ closedset s

definition connected (τ : topology X) := ∀ s, clopen s → (s = (space τ) ∨ s = ∅) 

end top

namespace subspaces

-- Show the subspace topology is an instance of a topology --

end subspaces

