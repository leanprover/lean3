import data.set
open algebra eq.ops set

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

namespace top

definition openset (τ : topology X) (s : set X) : Prop := s ∈ τ

definition closedset (τ : topology X) (s : set X) : Prop := openset τ (-s)

definition clopen (τ : topology X) (s : set X) : Prop := openset τ s ∧ closedset τ s

end top
