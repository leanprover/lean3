/-
Copyright (c) 2016 Andrew Zipperer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Zipperer, Jeremy Avigad

Basic group theory: subgroups, homomorphisms on a set, homomorphic images, cosets,
  normal cosets and the normalizer, the kernel of a homomorphism, the centralizer, etc.

For notation a * S and S * a for cosets, open the namespace "coset_notation".
For notation a^b and S^a, open the namespace "conj_notation".

TODO: homomorphisms on sets should be refactored and moved to algebra.
-/
import data.set algebra.homomorphism theories.move
open eq.ops set function

namespace group_theory

variables {A B C : Type}

/- subgroups -/

structure is_one_closed [class] [has_one A] (S : set A) : Prop :=
(one_mem : one ∈ S)

proposition one_mem [has_one A] {S : set A} [is_one_closed S] : 1 ∈ S :=
is_one_closed.one_mem _ S

structure is_mul_closed [class] [has_mul A] (S : set A) : Prop :=
(mul_mem : ∀₀ a ∈ S, ∀₀ b ∈ S, a * b ∈ S)

proposition mul_mem [has_mul A] {S : set A} [is_mul_closed S] {a b : A} (aS : a ∈ S) (bS : b ∈ S) :
  a * b ∈ S :=
is_mul_closed.mul_mem _ S aS bS

structure is_inv_closed [class] [has_inv A] (S : set A) : Prop :=
(inv_mem : ∀₀ a ∈ S, a⁻¹ ∈ S)

proposition inv_mem [has_inv A] {S : set A} [is_inv_closed S] {a : A} (aS : a ∈ S) : a⁻¹ ∈ S :=
is_inv_closed.inv_mem _ S aS

structure is_subgroup [class] [group A] (S : set A)
  extends is_one_closed S, is_mul_closed S, is_inv_closed S : Prop

section groupA
  variable [group A]

  proposition mem_of_inv_mem {a : A} {S : set A} [is_subgroup S] (H : a⁻¹ ∈ S) : a ∈ S :=
  have (a⁻¹)⁻¹ ∈ S, from inv_mem H,
  by rewrite inv_inv at this; apply this

  proposition inv_mem_iff (a : A) (S : set A) [is_subgroup S] : a⁻¹ ∈ S ↔ a ∈ S :=
  iff.intro mem_of_inv_mem inv_mem

  proposition is_subgroup_univ [instance] : is_subgroup (@univ A) :=
  ⦃ is_subgroup,
    one_mem := trivial,
    mul_mem := λ a au b bu, trivial,
    inv_mem := λ a au, trivial ⦄

  proposition is_subgroup_inter [instance] (G H : set A) [is_subgroup G] [is_subgroup H] :
    is_subgroup (G ∩ H) :=
  ⦃ is_subgroup,
    one_mem := and.intro one_mem one_mem,
    mul_mem := λ a ai b bi, and.intro (mul_mem (and.left ai) (and.left bi))
                   (mul_mem (and.right ai) (and.right bi)),
    inv_mem := λ a ai, and.intro (inv_mem (and.left ai)) (inv_mem (and.right ai)) ⦄
end groupA


/- homomorphisms on sets -/

section has_mulABC
  variables [has_mul A] [has_mul B] [has_mul C]

  -- in group theory, we can use is_hom for is_mul_hom
  abbreviation is_hom := @is_mul_hom

  definition is_hom_on [class] (f : A → B) (S : set A) : Prop :=
    ∀₀ a₁ ∈ S, ∀₀ a₂ ∈ S, f (a₁ * a₂) = f a₁ * f a₂

  proposition hom_on_mul (f : A → B) {S : set A} [H : is_hom_on f S] {a₁ a₂ : A}
      (a₁S : a₁ ∈ S) (a₂S : a₂ ∈ S) : f (a₁ * a₂) = (f a₁) * (f a₂) :=
    H a₁S a₂S

  proposition is_hom_on_of_is_hom (f : A → B) (S : set A) [H : is_hom f] : is_hom_on f S :=
  forallb_of_forall₂ S S (hom_mul f)

  proposition is_hom_of_is_hom_on_univ (f : A → B) [H : is_hom_on f univ] : is_hom f :=
  is_mul_hom.mk (forall_of_forallb_univ₂ H)

  proposition is_hom_on_univ_iff (f : A → B) : is_hom_on f univ ↔ is_hom f :=
  iff.intro (λH, is_hom_of_is_hom_on_univ f) (λ H, is_hom_on_of_is_hom f univ)

  proposition is_hom_on_of_subset (f : A → B) {S T : set A} (ssubt : S ⊆ T) [H : is_hom_on f T] :
    is_hom_on f S :=
  forallb_of_subset₂ ssubt ssubt H

  proposition is_hom_on_id (S : set A) : is_hom_on id S :=
  have H : is_hom (@id A), from is_mul_hom_id,
  is_hom_on_of_is_hom id S

  proposition is_hom_on_comp {S : set A} {T : set B} {g : B → C} {f : A → B}
    (H₁ : is_hom_on f S) (H₂ : is_hom_on g T) (H₃ : maps_to f S T) : is_hom_on (g ∘ f) S :=
  take a₁, assume a₁S, take a₂, assume a₂S,
  have f a₁ ∈ T, from H₃ a₁S,
  have f a₂ ∈ T, from H₃ a₂S,
  show g (f (a₁ * a₂)) = g (f a₁) * g (f a₂), by rewrite [H₁ a₁S a₂S, H₂ `f a₁ ∈ T` `f a₂ ∈ T`]
end has_mulABC

section groupAB
  variables [group A] [group B]

  proposition hom_on_one (f : A → B) (G : set A) [is_subgroup G] [H : is_hom_on f G] : f 1 = 1 :=
  have f 1 * f 1 = f 1 * 1, by rewrite [-H one_mem one_mem, *mul_one],
  eq_of_mul_eq_mul_left' this

  proposition hom_on_inv (f : A → B) {G : set A} [is_subgroup G] [H : is_hom_on f G]
      {a : A} (aG : a ∈ G) :
    f a⁻¹ = (f a)⁻¹ :=
  have f a⁻¹ * f a = 1, by rewrite [-H (inv_mem aG) aG, mul.left_inv, hom_on_one f G],
  eq_inv_of_mul_eq_one this

  proposition is_subgroup_image [instance] (f : A → B) (G : set A)
    [is_subgroup G] [is_hom_on f G] :
  is_subgroup (f ' G) :=
  ⦃ is_subgroup,
    one_mem := mem_image one_mem (hom_on_one f G),
    mul_mem := λ a afG b bfG,
      obtain c (cG : c ∈ G)(Hc : f c = a), from afG,
      obtain d (dG : d ∈ G)(Hd : f d = b), from bfG,
      show a * b ∈ f ' G, from mem_image (mul_mem cG dG) (by rewrite [hom_on_mul f cG dG, Hc, Hd]),
    inv_mem := λ a afG,
      obtain c (cG : c ∈ G)(Hc : f c = a), from afG,
      show a⁻¹ ∈ f ' G, from mem_image (inv_mem cG) (by rewrite [hom_on_inv f cG, Hc]) ⦄
end groupAB


/- cosets -/

definition lcoset [has_mul A] (a : A) (N : set A) : set A := (mul a) 'N
definition rcoset [has_mul A] (N : set A) (a : A) : set A := (mul^~ a) 'N

-- overload multiplication
namespace coset_notation
  infix * := lcoset
  infix * := rcoset
end coset_notation

open coset_notation

section has_mulA
  variable [has_mul A]

  proposition mul_mem_lcoset {S : set A} {x : A} (a : A) (xS : x ∈ S) : a * x ∈ a * S :=
  mem_image_of_mem (mul a) xS

  proposition mul_mem_rcoset [has_mul A] {S : set A} {x : A} (xS : x ∈ S) (a : A) :
    x * a ∈ S * a :=
  mem_image_of_mem (mul^~ a) xS

  definition lcoset_equiv (S : set A) (a b : A) : Prop := a * S = b * S

  proposition equivalence_lcoset_equiv (S : set A) : equivalence (lcoset_equiv S) :=
  mk_equivalence (lcoset_equiv S) (λ a, rfl) (λ a b, !eq.symm) (λ a b c, !eq.trans)

  proposition lcoset_subset_lcoset {S T : set A} (a : A) (H : S ⊆ T) : a * S ⊆ a * T :=
  image_subset _ H

  proposition rcoset_subset_rcoset {S T : set A} (H : S ⊆ T) (a : A) : S * a ⊆ T * a :=
  image_subset _ H

  proposition image_lcoset_of_is_hom_on {B : Type} [has_mul B] {f : A → B} {S : set A} {a : A}
      {G : set A} (SsubG : S ⊆ G) (aG : a ∈ G) [is_hom_on f G] :
    f ' (a * S) = f a * f ' S :=
  ext (take x, iff.intro
    (assume fas : x ∈ f ' (a * S),
      obtain t [s (sS : s ∈ S) (seq : a * s = t)] (teq : f t = x), from fas,
      have x = f a * f s, by rewrite [-teq, -seq, hom_on_mul f aG (SsubG sS)],
      show x ∈ f a * f ' S, by rewrite this; apply mul_mem_lcoset _ (mem_image_of_mem _ sS))
    (assume fafs : x ∈ f a * f ' S,
      obtain t [s (sS : s ∈ S) (seq : f s = t)] (teq : f a * t = x), from fafs,
      have x = f (a * s), by rewrite [-teq, -seq, hom_on_mul f aG (SsubG sS)],
      show x ∈ f ' (a * S), by rewrite this; exact mem_image_of_mem _ (mul_mem_lcoset _ sS)))

  proposition image_rcoset_of_is_hom_on {B : Type} [has_mul B] {f : A → B} {S : set A} {a : A}
    {G : set A} (SsubG : S ⊆ G) (aG : a ∈ G) [is_hom_on f G] :
  f ' (S * a) = f ' S * f a :=
  ext (take x, iff.intro
    (assume fas : x ∈ f ' (S * a),
      obtain t [s (sS : s ∈ S) (seq : s * a = t)] (teq : f t = x), from fas,
      have x = f s * f a, by rewrite [-teq, -seq, hom_on_mul f (SsubG sS) aG],
      show x ∈ f ' S * f a, by rewrite this; exact mul_mem_rcoset (mem_image_of_mem _ sS) _)
    (assume fafs : x ∈ f ' S * f a,
      obtain t [s (sS : s ∈ S) (seq : f s = t)] (teq : t * f a = x), from fafs,
      have x = f (s * a), by rewrite [-teq, -seq, hom_on_mul f (SsubG sS) aG],
      show x ∈ f ' (S * a), by rewrite this; exact mem_image_of_mem _ (mul_mem_rcoset sS _)))

  proposition image_lcoset_of_is_hom {B : Type} [has_mul B] (f : A → B) (a : A) (S : set A)
      [is_hom f] :
    f ' (a * S) = f a * f ' S :=
  have is_hom_on f univ, from is_hom_on_of_is_hom f univ,
  image_lcoset_of_is_hom_on (subset_univ S) !mem_univ

  proposition image_rcoset_of_is_hom {B : Type} [has_mul B] (f : A → B) (S : set A) (a : A)
      [is_hom f] :
    f ' (S * a) = f ' S * f a :=
  have is_hom_on f univ, from is_hom_on_of_is_hom f univ,
  image_rcoset_of_is_hom_on (subset_univ S) !mem_univ
end has_mulA

section semigroupA
  variable [semigroup A]

  proposition rcoset_rcoset (S : set A) (a b : A) : S * a * b = S * (a * b) :=
  have H : (mul^~ b) ∘ (mul^~ a) = mul^~ (a * b), from funext (take x, !mul.assoc),
  calc
    S * a * b = ((mul^~ b) ∘ (mul^~ a)) 'S : image_comp
          ... = S * (a * b)                : by rewrite [↑rcoset, H]

  proposition lcoset_lcoset (S : set A) (a b : A) : a * (b * S)  = (a * b) * S :=
  have H : (mul a) ∘ (mul b) = mul (a * b), from funext (take x, !mul.assoc⁻¹),
  calc
    a * (b * S) = ((mul a) ∘ (mul b)) 'S : image_comp
            ... = (a * b) * S            : by rewrite [↑lcoset, H]

  proposition lcoset_rcoset [semigroup A] (S : set A) (a b : A) : a * S * b = a * (S * b) :=
  have H : (mul^~ b) ∘ (mul a) = (mul a) ∘ (mul^~ b), from funext (take x, !mul.assoc),
  calc
    a * S * b = ((mul^~ b) ∘ (mul a)) 'S : image_comp
          ... = ((mul a) ∘ (mul^~ b)) 'S : H
          ... = a * (S * b)              : image_comp
end semigroupA

section monoidA
  variable [monoid A]

  proposition one_lcoset (S : set A) : 1 * S = S :=
  ext (take x, iff.intro
    (suppose x ∈ 1 * S,
      obtain s (sS : s ∈ S) (eqx : 1 * s = x), from this,
      show x ∈ S, by rewrite [-eqx, one_mul]; apply sS)
    (suppose x ∈ S,
      have 1 * x ∈ 1 * S, from mem_image_of_mem (mul 1) this,
      show x ∈ 1 * S, by rewrite one_mul at this; apply this))

  proposition rcoset_one (S : set A) : S * 1 = S :=
  ext (take x, iff.intro
    (suppose x ∈ S * 1,
      obtain s (sS : s ∈ S) (eqx : s * 1 = x), from this,
      show x ∈ S, by rewrite [-eqx, mul_one]; apply sS)
    (suppose x ∈ S,
      have x * 1 ∈ S * 1, from mem_image_of_mem (mul^~ 1) this,
      show x ∈ S * 1, by rewrite mul_one at this; apply this))
end monoidA

section groupA
  variable [group A]

  proposition lcoset_inv_lcoset (a : A) (S : set A) : a * (a⁻¹ * S) = S :=
  by rewrite [lcoset_lcoset, mul.right_inv, one_lcoset]

  proposition inv_lcoset_lcoset (a : A) (S : set A) : a⁻¹ * (a * S) = S :=
  by rewrite [lcoset_lcoset, mul.left_inv, one_lcoset]

  proposition rcoset_inv_rcoset (S : set A) (a : A) : (S * a⁻¹) * a = S :=
  by rewrite [rcoset_rcoset, mul.left_inv, rcoset_one]

  proposition rcoset_rcoset_inv (S : set A) (a : A) : (S * a) * a⁻¹ = S :=
  by rewrite [rcoset_rcoset, mul.right_inv, rcoset_one]

  proposition eq_of_lcoset_eq_lcoset {a : A} {S T : set A} (H : a * S = a * T) : S = T :=
  by rewrite [-inv_lcoset_lcoset a S, -inv_lcoset_lcoset a T, H]

  proposition eq_of_rcoset_eq_rcoset {a : A} {S T : set A} (H : S * a = T * a) : S = T :=
  by rewrite [-rcoset_rcoset_inv S a, -rcoset_rcoset_inv T a, H]

  proposition mem_of_mul_mem_lcoset {a b : A} {S : set A} (abaS : a * b ∈ a * S) : b ∈ S :=
  have a⁻¹ * (a * b) ∈ a⁻¹ * (a * S), from mul_mem_lcoset _ abaS,
  by rewrite [inv_mul_cancel_left at this, inv_lcoset_lcoset at this]; apply this

  proposition mul_mem_lcoset_iff (a b : A) (S : set A) : a * b ∈ a * S ↔ b ∈ S :=
  iff.intro !mem_of_mul_mem_lcoset !mul_mem_lcoset

  proposition mem_of_mul_mem_rcoset {a b : A} {S : set A} (abSb : a * b ∈ S * b) : a ∈ S :=
  have (a * b) * b⁻¹ ∈ (S * b) * b⁻¹, from mul_mem_rcoset abSb _,
  by rewrite [mul_inv_cancel_right at this, rcoset_rcoset_inv at this]; apply this

  proposition mul_mem_rcoset_iff (a b : A) (S : set A) : a * b ∈ S * b ↔ a ∈ S :=
  iff.intro !mem_of_mul_mem_rcoset (λ H, mul_mem_rcoset H _)

  proposition inv_mul_mem_of_mem_lcoset {a b : A} {S : set A} (abS : a ∈ b * S) : b⁻¹ * a ∈ S :=
  have b⁻¹ * a ∈ b⁻¹ * (b * S), from mul_mem_lcoset b⁻¹ abS,
  by rewrite inv_lcoset_lcoset at this; apply this

  proposition mem_lcoset_of_inv_mul_mem {a b : A} {S : set A} (H : b⁻¹ * a ∈ S) : a ∈ b * S :=
  have b * (b⁻¹ * a) ∈ b * S, from mul_mem_lcoset b H,
  by rewrite mul_inv_cancel_left at this; apply this

  proposition mem_lcoset_iff (a b : A) (S : set A) : a ∈ b * S ↔ b⁻¹ * a ∈ S :=
  iff.intro inv_mul_mem_of_mem_lcoset mem_lcoset_of_inv_mul_mem

  proposition mul_inv_mem_of_mem_rcoset {a b : A} {S : set A} (aSb : a ∈ S * b) : a * b⁻¹ ∈ S :=
  have a * b⁻¹ ∈ (S * b) * b⁻¹, from mul_mem_rcoset aSb b⁻¹,
  by rewrite rcoset_rcoset_inv at this; apply this

  proposition mem_rcoset_of_mul_inv_mem {a b : A} {S : set A} (H : a * b⁻¹ ∈ S) : a ∈ S * b :=
  have a * b⁻¹ * b ∈ S * b, from mul_mem_rcoset H b,
  by rewrite inv_mul_cancel_right at this; apply this

  proposition mem_rcoset_iff (a b : A) (S : set A) : a ∈ S * b ↔ a * b⁻¹ ∈ S :=
  iff.intro mul_inv_mem_of_mem_rcoset mem_rcoset_of_mul_inv_mem

  proposition lcoset_eq_iff_eq_inv_lcoset (a : A) (S T : set A) : (a * S = T) ↔ (S = a⁻¹ * T) :=
  iff.intro (assume H, by rewrite [-H, inv_lcoset_lcoset])
      (assume H, by rewrite [H, lcoset_inv_lcoset])

  proposition rcoset_eq_iff_eq_rcoset_inv (a : A) (S T : set A) : (S * a = T) ↔ (S = T * a⁻¹) :=
  iff.intro (assume H, by rewrite [-H, rcoset_rcoset_inv])
      (assume H, by rewrite [H, rcoset_inv_rcoset])

  proposition lcoset_inter (a : A) (S T : set A) [is_subgroup S] [is_subgroup T] :
    a * (S ∩ T) = (a * S) ∩ (a * T) :=
  eq_of_subset_of_subset
    (image_inter_subset _ S T)
    (take b, suppose b ∈ (a * S) ∩ (a * T),
      obtain [s [smem (seq : a * s = b)]] [t [tmem (teq : a * t = b)]], from this,
      have s = t, from eq_of_mul_eq_mul_left' (eq.trans seq (eq.symm teq)),
      show b ∈ a * (S ∩ T),
        begin
          rewrite -seq,
          apply mul_mem_lcoset,
          apply and.intro smem,
          rewrite this, apply tmem
        end)

  proposition inter_rcoset (a : A) (S T : set A) [is_subgroup S] [is_subgroup T] :
    (S ∩ T) * a = (S * a) ∩ (T * a) :=
  eq_of_subset_of_subset
    (image_inter_subset _ S T)
    (take b, suppose b ∈ (S * a) ∩ (T * a),
      obtain [s [smem (seq : s * a = b)]] [t [tmem (teq : t * a = b)]], from this,
      have s = t, from eq_of_mul_eq_mul_right' (eq.trans seq (eq.symm teq)),
      show b ∈ (S ∩ T) * a,
        begin
          rewrite -seq,
          apply mul_mem_rcoset,
          apply and.intro smem,
          rewrite this, apply tmem
        end)
end groupA

section subgroupG
  variables [group A] {G : set A} [is_subgroup G]

  proposition lcoset_eq_self_of_mem {a : A} (aG : a ∈ G) : a * G = G :=
  ext (take x, iff.intro
    (assume xaG, obtain g [gG xeq], from xaG,
      show x ∈ G, by rewrite -xeq; exact (mul_mem aG gG))
    (assume xG, show x ∈ a * G, from mem_image
      (show a⁻¹ * x ∈ G, from (mul_mem (inv_mem aG) xG)) !mul_inv_cancel_left))

  proposition rcoset_eq_self_of_mem {a : A} (aG : a ∈ G) : G * a = G :=
  ext (take x, iff.intro
    (assume xGa, obtain g [gG xeq], from xGa,
      show x ∈ G, by rewrite -xeq; exact (mul_mem gG aG))
    (assume xG, show x ∈ G * a, from mem_image
      (show x * a⁻¹ ∈ G, from (mul_mem xG (inv_mem aG))) !inv_mul_cancel_right))

  proposition mem_lcoset_self (a : A) : a ∈ a * G :=
  by rewrite [-mul_one a at {1}]; exact mul_mem_lcoset a one_mem

  proposition mem_rcoset_self (a : A) : a ∈ G * a :=
  by rewrite [-one_mul a at {1}]; exact mul_mem_rcoset one_mem a

  proposition mem_of_lcoset_eq_self {a : A} (H : a * G = G) : a ∈ G :=
  by rewrite [-H]; exact mem_lcoset_self a

  proposition mem_of_rcoset_eq_self {a : A} (H : G * a = G) : a ∈ G :=
  by rewrite [-H]; exact mem_rcoset_self a

  variable (G)

  proposition lcoset_eq_self_iff (a : A) : a * G = G ↔ a ∈ G :=
  iff.intro mem_of_lcoset_eq_self lcoset_eq_self_of_mem

  proposition rcoset_eq_self_iff (a : A) : G * a = G ↔ a ∈ G :=
  iff.intro mem_of_rcoset_eq_self rcoset_eq_self_of_mem

  variable {G}

  proposition lcoset_eq_lcoset {a b : A} (H : b⁻¹ * a ∈ G) : a * G = b * G :=
  have b⁻¹ * (a * G) = b⁻¹ * (b * G),
    by rewrite [inv_lcoset_lcoset, lcoset_lcoset, lcoset_eq_self_of_mem H],
  eq_of_lcoset_eq_lcoset this

  proposition inv_mul_mem_of_lcoset_eq_lcoset {a b : A} (H : a * G = b * G) : b⁻¹ * a ∈ G :=
  mem_of_lcoset_eq_self (by rewrite [-lcoset_lcoset, H, inv_lcoset_lcoset])

  proposition lcoset_eq_lcoset_iff (a b : A) : a * G = b * G ↔ b⁻¹ * a ∈ G :=
  iff.intro inv_mul_mem_of_lcoset_eq_lcoset lcoset_eq_lcoset

  proposition rcoset_eq_rcoset {a b : A} (H : a * b⁻¹ ∈ G) : G * a = G * b :=
  have G * a * b⁻¹ = G * b * b⁻¹,
    by rewrite [rcoset_rcoset_inv, rcoset_rcoset, rcoset_eq_self_of_mem H],
  eq_of_rcoset_eq_rcoset this

  proposition mul_inv_mem_of_rcoset_eq_rcoset {a b : A} (H : G * a = G * b) : a * b⁻¹ ∈ G :=
  mem_of_rcoset_eq_self (by rewrite [-rcoset_rcoset, H, rcoset_rcoset_inv])

  proposition rcoset_eq_rcoset_iff (a b : A) : G * a = G * b ↔ a * b⁻¹ ∈ G :=
  iff.intro mul_inv_mem_of_rcoset_eq_rcoset rcoset_eq_rcoset
end subgroupG


/- normal cosets and the normalizer -/

section has_mulA
  variable [has_mul A]

  abbreviation normalizes [reducible] (a : A) (S : set A) : Prop := a * S = S * a

  definition is_normal [class] (S : set A) : Prop := ∀ a, normalizes a S

  definition normalizer (S : set A) : set A := { a : A | normalizes a S }

  definition is_normal_in [class] (S T : set A) : Prop := T ⊆ normalizer S

  abbreviation normalizer_in [reducible] (S T : set A) : set A := T ∩ normalizer S

  proposition lcoset_eq_rcoset (a : A) (S : set A) [H : is_normal S] : a * S = S * a := H a

  proposition subset_normalizer (S T : set A) [H : is_normal_in T S] : S ⊆ normalizer T := H

  proposition lcoset_eq_rcoset_of_mem {a : A} (S : set A) {T : set A} [H : is_normal_in S T]
      (amemT : a ∈ T) :
    a * S = S * a := H amemT

  proposition is_normal_in_of_is_normal (S T : set A) [H : is_normal S] : is_normal_in S T :=
  forallb_of_forall T H

  proposition is_normal_of_is_normal_in_univ {S : set A} (H : is_normal_in S univ) :
    is_normal S :=
  forall_of_forallb_univ H

  proposition is_normal_in_univ_iff_is_normal (S : set A) : is_normal_in S univ ↔ is_normal S :=
  forallb_univ_iff_forall _

   proposition is_normal_in_of_subset {S T U : set A} (H : T ⊆ U) (H' : is_normal_in S U) :
    is_normal_in S T :=
  forallb_of_subset H H'

  proposition normalizes_of_mem_normalizer {a : A} {S : set A} (H : a ∈ normalizer S) :
    normalizes a S := H

  proposition mem_normalizer_iff_normalizes (a : A) (S : set A) :
    a ∈ normalizer S ↔ normalizes a S := iff.refl _

  proposition is_normal_in_normalizer [instance] (S : set A) : is_normal_in S (normalizer S) :=
  subset.refl (normalizer S)
end has_mulA

section groupA
  variable [group A]

  proposition is_normal_in_of_forall_subset {S G : set A} [is_subgroup G]
    (H : ∀₀ x ∈ G, x * S ⊆ S * x) :
  is_normal_in S G :=
  take x, assume xG,
  show x * S = S * x, from eq_of_subset_of_subset (H xG)
    (have x * (x⁻¹ * S) * x ⊆ x * (S * x⁻¹) * x,
      from rcoset_subset_rcoset (lcoset_subset_lcoset x (H (inv_mem xG))) x,
      show S * x ⊆ x * S,
        begin
         rewrite [lcoset_inv_lcoset at this, lcoset_rcoset at this, rcoset_inv_rcoset at this],
         exact this
       end)

  proposition is_normal_of_forall_subset {S : set A} (H : ∀ x, x * S ⊆ S * x) : is_normal S :=
  begin
    rewrite [-is_normal_in_univ_iff_is_normal],
    apply is_normal_in_of_forall_subset,
    intro x xuniv, exact H x
  end

  proposition subset_normalizer_self (G : set A) [is_subgroup G] : G ⊆ normalizer G :=
  take a, assume aG, show a * G = G * a,
    by rewrite [lcoset_eq_self_of_mem aG, rcoset_eq_self_of_mem aG]
end groupA

section normalG
  variables [group A] (G : set A) [is_normal G]

  proposition lcoset_equiv_mul {a₁ a₂ b₁ b₂ : A}
    (H₁ : lcoset_equiv G a₁ a₂) (H₂ : lcoset_equiv G b₁ b₂) : lcoset_equiv G (a₁ * b₁) (a₂ * b₂) :=
  begin
    unfold lcoset_equiv at *,
    rewrite [-lcoset_lcoset, H₂, lcoset_eq_rcoset, -lcoset_rcoset, H₁, lcoset_rcoset,
             -lcoset_eq_rcoset, lcoset_lcoset]
  end

  proposition lcoset_equiv_inv {a₁ a₂ : A} (H : lcoset_equiv G a₁ a₂) : lcoset_equiv G a₁⁻¹ a₂⁻¹ :=
  begin
    unfold lcoset_equiv at *,
    have a₁⁻¹ * G = a₂⁻¹ * (a₂ * G) * a₁⁻¹, by rewrite [inv_lcoset_lcoset, lcoset_eq_rcoset],
    rewrite [this, -H, lcoset_rcoset, lcoset_eq_rcoset, rcoset_rcoset_inv]
  end
end normalG


/- the normalizer is a subgroup -/

section semigroupA
  variable [semigroup A]

  proposition mul_mem_normalizer {S : set A} {a b : A}
    (Ha : a ∈ normalizer S) (Hb : b ∈ normalizer S) : a * b ∈ normalizer S :=
  show a * b * S = S * (a * b),
    by rewrite [-lcoset_lcoset, normalizes_of_mem_normalizer Hb, -lcoset_rcoset,
                normalizes_of_mem_normalizer Ha, rcoset_rcoset]
end semigroupA

section monoidA
  variable [monoid A]

  proposition one_mem_normalizer (S : set A) : 1 ∈ normalizer S :=
  by rewrite [↑normalizer, mem_set_of_iff, one_lcoset, rcoset_one]
end monoidA

section groupA
  variable [group A]

  proposition inv_mem_normalizer {S : set A} {a : A} (H : a ∈ normalizer S) : a⁻¹ ∈ normalizer S :=
  have a⁻¹ * S = S * a⁻¹,
  begin
    apply iff.mp (rcoset_eq_iff_eq_rcoset_inv _ _ _),
    rewrite [lcoset_rcoset, -normalizes_of_mem_normalizer H, inv_lcoset_lcoset]
  end,
  by rewrite [↑normalizer, mem_set_of_iff, this]

  proposition is_subgroup_normalizer [instance] (S : set A) : is_subgroup (normalizer S) :=
  ⦃ is_subgroup,
    one_mem := one_mem_normalizer S,
    mul_mem := λ a Ha b Hb, mul_mem_normalizer Ha Hb,
    inv_mem := λ a H, inv_mem_normalizer H⦄
end groupA

section subgroupG
  variables [group A] {G : set A} [is_subgroup G]

  proposition normalizes_image_of_is_hom_on [group B] {a : A} (aG : a ∈ G) {S : set A}
      (SsubG : S ⊆ G) (H : normalizes a S) (f : A → B) [is_hom_on f G] :
    normalizes (f a) (f ' S) :=
  by rewrite [-image_lcoset_of_is_hom_on SsubG aG, -image_rcoset_of_is_hom_on SsubG aG,
              ↑normalizes at H, H]

  proposition is_normal_in_image_image [group B] {S T : set A} (SsubT : S ⊆ T)
      [H : is_normal_in S T] (f : A → B) [is_subgroup T] [is_hom_on f T] :
    is_normal_in (f ' S) (f ' T) :=
  take a, assume afT,
  obtain b [bT (beq : f b = a)], from afT,
  show normalizes a (f ' S),
    begin rewrite -beq, apply (normalizes_image_of_is_hom_on bT SsubT (H bT)) end

  proposition normalizes_image_of_is_hom [group B] {a : A} {S : set A}
      (H : normalizes a S) (f : A → B) [is_hom f] :
    normalizes (f a) (f ' S) :=
  by rewrite [-image_lcoset_of_is_hom f a S, -image_rcoset_of_is_hom f S a,
              ↑normalizes at H, H]

  proposition is_normal_in_image_image_univ [group B] {S : set A}
      [H : is_normal S] (f : A → B) [is_hom f] :
    is_normal_in (f ' S) (f ' univ) :=
  take a, assume afT,
  obtain b [buniv (beq : f b = a)], from afT,
  show normalizes a (f ' S),
    begin rewrite -beq, apply (normalizes_image_of_is_hom (H b) f) end
end subgroupG


/- conjugation -/

definition conj [reducible] [group A] (a b : A) : A := b⁻¹ * a * b

definition set_conj [reducible] [group A] (S : set A)(a : A) : set A := a⁻¹ * S * a
-- conj^~ a ' S

namespace conj_notation
  infix `^` := conj
  infix `^` := set_conj
end conj_notation

open conj_notation

section groupA
  variables [group A]

  proposition set_conj_eq_image_conj (S : set A) (a : A) : S^a = conj^~ a 'S :=
  eq.symm !image_comp

  proposition set_conj_eq_self_of_normalizes {S : set A} {a : A} (H : normalizes a S) : S^a = S :=
  by rewrite [lcoset_rcoset, ↑normalizes at H, -H, inv_lcoset_lcoset]

  proposition normalizes_of_set_conj_eq_self {S : set A} {a : A} (H : S^a = S) : normalizes a S :=
  by rewrite [-H at {1}, ↑set_conj, lcoset_rcoset, lcoset_inv_lcoset]

  proposition set_conj_eq_self_iff_normalizes (S : set A) (a : A) : S^a = S ↔ normalizes a S :=
  iff.intro normalizes_of_set_conj_eq_self set_conj_eq_self_of_normalizes

  proposition set_conj_eq_self_of_mem_normalizer {S : set A} {a : A} (H : a ∈ normalizer S) :
    S^a = S := set_conj_eq_self_of_normalizes H

  proposition mem_normalizer_of_set_conj_eq_self {S : set A} {a : A} (H : S^a = S) :
    a ∈ normalizer S := normalizes_of_set_conj_eq_self H

  proposition set_conj_eq_self_iff_mem_normalizer (S : set A) (a : A) :
    S^a = S ↔ a ∈ normalizer S :=
  iff.intro mem_normalizer_of_set_conj_eq_self set_conj_eq_self_of_mem_normalizer

  proposition conj_one (a : A) : a ^ (1 : A) = a :=
  by rewrite [↑conj, one_inv, one_mul, mul_one]

  proposition conj_conj (a b c : A) : (a^b)^c = a^(b * c) :=
  by rewrite [↑conj, mul_inv, *mul.assoc]

  proposition conj_inv (a b : A) : (a^b)⁻¹ = (a⁻¹)^b :=
  by rewrite[mul_inv, mul_inv, inv_inv, mul.assoc]

  proposition mul_conj (a b c : A) : (a * b)^c = a^c * b^c :=
  by rewrite[↑conj, *mul.assoc, mul_inv_cancel_left]
end groupA


/- the kernel -/

definition ker [has_one B] (f : A → B) : set A := { x | f x = 1 }

section hasoneB
  variable [has_one B]

  proposition eq_one_of_mem_ker {f : A → B} {a : A} (H : a ∈ ker f) : f a = 1 := H

  proposition mem_ker_iff (f : A → B) (a : A) : a ∈ ker f ↔ f a = 1 := iff.rfl

  proposition ker_eq_preimage_one (f : A → B) : ker f = f '- '{1} :=
  ext (take x, by rewrite [mem_ker_iff, -mem_preimage_iff, mem_singleton_iff])

  definition ker_in (f : A → B) (S : set A) : set A := ker f ∩ S

  proposition ker_in_univ (f : A → B) : ker_in f univ = ker f :=
  !inter_univ
end hasoneB

section groupAB
  variables [group A] [group B]
  variable  {f : A → B}

  proposition eq_of_mul_inv_mem_ker [is_hom f] {a₁ a₂ : A} (H : a₁ * a₂⁻¹ ∈ ker f) :
    f a₁ = f a₂ :=
  eq_of_mul_inv_eq_one (by rewrite [-hom_inv f, -hom_mul f]; exact H)

  proposition mul_inv_mem_ker_of_eq [is_hom f] {a₁ a₂ : A} (H : f a₁ = f a₂) :
    a₁ * a₂⁻¹ ∈ ker f :=
  show f (a₁ * a₂⁻¹) = 1, by rewrite [hom_mul f, hom_inv f, H, mul.right_inv]

  proposition eq_iff_mul_inv_mem_ker [is_hom f] (a₁ a₂ : A) : f a₁ = f a₂ ↔ a₁ * a₂⁻¹ ∈ ker f :=
  iff.intro mul_inv_mem_ker_of_eq eq_of_mul_inv_mem_ker

  proposition eq_of_mul_inv_mem_ker_in {G : set A} [is_subgroup G] [is_hom_on f G]
      {a₁ a₂ : A} (a₁G : a₁ ∈ G) (a₂G : a₂ ∈ G) (H : a₁ * a₂⁻¹ ∈ ker_in f G) :
    f a₁ = f a₂ :=
  eq_of_mul_inv_eq_one (by rewrite [-hom_on_inv f a₂G, -hom_on_mul f a₁G (inv_mem a₂G)];
    exact and.left H)

  proposition mul_inv_mem_ker_in_of_eq {G : set A} [is_subgroup G] [is_hom_on f G]
      {a₁ a₂ : A} (a₁G : a₁ ∈ G) (a₂G : a₂ ∈ G) (H : f a₁ = f a₂) :
    a₁ * a₂⁻¹ ∈ ker_in f G :=
  and.intro
    (show f (a₁ * a₂⁻¹) = 1,
      by rewrite [hom_on_mul f a₁G (inv_mem a₂G), hom_on_inv f a₂G, H, mul.right_inv])
    (mul_mem a₁G (inv_mem a₂G))

  proposition eq_iff_mul_inv_mem_ker_in {G : set A} [is_subgroup G] [is_hom_on f G]
      {a₁ a₂ : A} (a₁G : a₁ ∈ G) (a₂G : a₂ ∈ G) :
    f a₁ = f a₂ ↔ a₁ * a₂⁻¹ ∈ ker_in f G :=
  iff.intro (mul_inv_mem_ker_in_of_eq a₁G a₂G) (eq_of_mul_inv_mem_ker_in a₁G a₂G)

  -- Ouch! These versions are not equivalent to the ones before.

  proposition eq_of_inv_mul_mem_ker [is_hom f] {a₁ a₂ : A} (H : a₁⁻¹ * a₂ ∈ ker f) :
    f a₁ = f a₂ :=
  eq.symm (eq_of_inv_mul_eq_one (by rewrite [-hom_inv f, -hom_mul f]; exact H))

  proposition inv_mul_mem_ker_of_eq [is_hom f] {a₁ a₂ : A} (H : f a₁ = f a₂) :
    a₁⁻¹ * a₂ ∈ ker f :=
  show f (a₁⁻¹ * a₂) = 1, by rewrite [hom_mul f, hom_inv f, H, mul.left_inv]

  proposition eq_iff_inv_mul_mem_ker [is_hom f] (a₁ a₂ : A) : f a₁ = f a₂ ↔ a₁⁻¹ * a₂ ∈ ker f :=
  iff.intro inv_mul_mem_ker_of_eq eq_of_inv_mul_mem_ker

  proposition eq_of_inv_mul_mem_ker_in {G : set A} [is_subgroup G] [is_hom_on f G]
      {a₁ a₂ : A} (a₁G : a₁ ∈ G) (a₂G : a₂ ∈ G) (H : a₁⁻¹ * a₂ ∈ ker_in f G) :
    f a₁ = f a₂ :=
  eq.symm (eq_of_inv_mul_eq_one (by rewrite [-hom_on_inv f a₁G, -hom_on_mul f (inv_mem a₁G) a₂G];
    exact and.left H))

  proposition inv_mul_mem_ker_in_of_eq {G : set A} [is_subgroup G] [is_hom_on f G]
      {a₁ a₂ : A} (a₁G : a₁ ∈ G) (a₂G : a₂ ∈ G) (H : f a₁ = f a₂) :
    a₁⁻¹ * a₂ ∈ ker_in f G :=
  and.intro
    (show f (a₁⁻¹ * a₂) = 1,
      by rewrite [hom_on_mul f (inv_mem a₁G) a₂G, hom_on_inv f a₁G, H, mul.left_inv])
    (mul_mem (inv_mem a₁G) a₂G)

  proposition eq_iff_inv_mul_mem_ker_in {G : set A} [is_subgroup G] [is_hom_on f G]
      {a₁ a₂ : A} (a₁G : a₁ ∈ G) (a₂G : a₂ ∈ G) :
    f a₁ = f a₂ ↔ a₁⁻¹ * a₂ ∈ ker_in f G :=
  iff.intro (inv_mul_mem_ker_in_of_eq a₁G a₂G) (eq_of_inv_mul_mem_ker_in a₁G a₂G)

  proposition eq_one_of_eq_one_of_injective [is_hom f] (H : injective f) {x : A}
      (H' : f x = 1) :
    x = 1 :=
  H (by rewrite [H', hom_one f])

  proposition eq_one_iff_eq_one_of_injective [is_hom f] (H : injective f) (x : A) :
    f x = 1 ↔ x = 1 :=
  iff.intro (eq_one_of_eq_one_of_injective H) (λ H', by rewrite [H', hom_one f])

  proposition injective_of_forall_eq_one [is_hom f] (H : ∀ x, f x = 1 → x = 1) : injective f :=
  take a₁ a₂, assume Heq,
  have f (a₁ * a₂⁻¹) = 1, by rewrite [hom_mul f, hom_inv f, Heq, mul.right_inv],
  eq_of_mul_inv_eq_one (H _ this)

  proposition injective_of_ker_eq_singleton_one [is_hom f] (H : ker f = '{1}) : injective f :=
  injective_of_forall_eq_one
    (take x, suppose x ∈ ker f, by rewrite [H at this]; exact eq_of_mem_singleton this)

  proposition ker_eq_singleton_one_of_injective [is_hom f] (H : injective f) : ker f = '{1} :=
  ext (take x, by rewrite [mem_ker_iff, mem_singleton_iff, eq_one_iff_eq_one_of_injective H])

  variable (f)
  proposition injective_iff_ker_eq_singleton_one [is_hom f] : injective f ↔ ker f = '{1} :=
  iff.intro ker_eq_singleton_one_of_injective injective_of_ker_eq_singleton_one
  variable {f}

  proposition eq_one_of_eq_one_of_inj_on {G : set A} [is_subgroup G] [is_hom_on f G]
    (H : inj_on f G) {x : A} (xG : x ∈ G) (H' : f x = 1) :
    x = 1 :=
  H xG one_mem (by rewrite [H', hom_on_one f G])

  proposition eq_one_iff_eq_one_of_inj_on {G : set A} [is_subgroup G] [is_hom_on f G]
    (H : inj_on f G) {x : A} (xG : x ∈ G) [is_hom_on f G] :
    f x = 1 ↔ x = 1 :=
  iff.intro (eq_one_of_eq_one_of_inj_on H xG) (λ H', by rewrite [H', hom_on_one f G])

  proposition inj_on_of_forall_eq_one {G : set A} [is_subgroup G] [is_hom_on f G]
    (H : ∀₀ x ∈ G, f x = 1 → x = 1) : inj_on f G :=
  take a₁ a₂, assume a₁G a₂G Heq,
  have f (a₁ * a₂⁻¹) = 1,
    by rewrite [hom_on_mul f a₁G (inv_mem a₂G), hom_on_inv f a₂G, Heq, mul.right_inv],
  eq_of_mul_inv_eq_one (H (mul_mem a₁G (inv_mem a₂G)) this)

  proposition inj_on_of_ker_in_eq_singleton_one {G : set A} [is_subgroup G] [is_hom_on f G]
    (H : ker_in f G = '{1}) : inj_on f G :=
  inj_on_of_forall_eq_one
    (take x, assume xG fxone,
      have x ∈ ker_in f G, from and.intro fxone xG,
      by rewrite [H at this]; exact eq_of_mem_singleton this)

  proposition ker_in_eq_singleton_one_of_inj_on {G : set A} [is_subgroup G] [is_hom_on f G]
    (H : inj_on f G) : ker_in f G = '{1} :=
  ext (take x,
    begin
      rewrite [↑ker_in, mem_inter_iff, mem_ker_iff, mem_singleton_iff],
      apply iff.intro,
        {intro H', cases H' with fxone xG, exact eq_one_of_eq_one_of_inj_on H xG fxone},
      intro xone, rewrite xone, split, exact hom_on_one f G, exact one_mem
    end)

  variable (f)
  proposition inj_on_iff_ker_in_eq_singleton_one (G : set A) [is_subgroup G] [is_hom_on f G] :
    inj_on f G ↔ ker_in f G = '{1} :=
  iff.intro ker_in_eq_singleton_one_of_inj_on inj_on_of_ker_in_eq_singleton_one
  variable {f}

  proposition conj_mem_ker [is_hom f] {a₁ : A} (a₂ : A) (H : a₁ ∈ ker f) : a₁^a₂ ∈ ker f :=
  show f (a₁^a₂) = 1,
    by rewrite [↑conj, *(hom_mul f), hom_inv f, eq_one_of_mem_ker H, mul_one, mul.left_inv]

  variable (f)

  proposition is_subgroup_ker_in [instance] (S : set A) [is_subgroup S] [is_hom_on f S] :
    is_subgroup (ker_in f S) :=
  ⦃ is_subgroup,
    one_mem := and.intro (hom_on_one f S) one_mem,
    mul_mem := λ a aker b bker,
                 obtain (fa : f a = 1) (aS : a ∈ S), from aker,
                 obtain (fb : f b = 1) (bS : b ∈ S), from bker,
                 and.intro (show f (a * b) = 1, by rewrite [hom_on_mul f aS bS, fa, fb, one_mul])
                   (mul_mem aS bS),
    inv_mem := λ a aker,
                 obtain (fa : f a = 1) (aS : a ∈ S), from aker,
                 and.intro (show f (a⁻¹) = 1, by rewrite [hom_on_inv f aS, fa, one_inv])
                   (inv_mem aS)
  ⦄

  proposition is_subgroup_ker [instance] [is_hom f] : is_subgroup (ker f) :=
  begin
    rewrite [-ker_in_univ f],
    have is_hom_on f univ, from is_hom_on_of_is_hom f univ,
    apply is_subgroup_ker_in f univ
  end

  proposition is_normal_in_ker_in [instance] (G : set A) [is_subgroup G] [is_hom_on f G] :
    is_normal_in (ker_in f G) G :=
  is_normal_in_of_forall_subset
    (take x, assume xG, take y, assume yker,
      obtain z [[(fz : f z = 1) zG] (yeq : x * z = y)], from yker,
      have y = x * z * x⁻¹ * x, by rewrite [yeq, inv_mul_cancel_right],
      show y ∈ ker_in f G * x,
        begin
          rewrite this,
          apply mul_mem_rcoset,
          apply and.intro,
          show f (x * z * x⁻¹) = 1,
            by rewrite [hom_on_mul f (mul_mem xG zG) (inv_mem xG), hom_on_mul f xG zG, fz,
                        hom_on_inv f xG, mul_one, mul.right_inv],
          show x * z * x⁻¹ ∈ G, from mul_mem (mul_mem xG zG) (inv_mem xG)
        end)

  proposition is_normal_ker [instance] [H : is_hom f] : is_normal (ker f) :=
  begin
    rewrite [-ker_in_univ, -is_normal_in_univ_iff_is_normal],
    apply is_normal_in_ker_in,
    exact is_hom_on_of_is_hom f univ
  end

end groupAB

section subgroupH
  variables [group A] [group B] {H : set A} [is_subgroup H]
  variables {f : A → B} [is_hom f]

  proposition subset_ker_of_forall (hyp : ∀ x y, x * H = y * H → f x = f y) : H ⊆ ker f :=
  take h, assume hH,
  have h * H = 1 * H, by rewrite [lcoset_eq_self_of_mem hH, one_lcoset],
  have f h = f 1, from hyp h 1 this,
  show f h = 1, by rewrite [this, hom_one f]

  proposition eq_of_lcoset_eq_lcoset_of_subset_ker {x y : A} (hyp₀ : x * H = y * H) (hyp₁ : H ⊆ ker f) :
    f x = f y :=
  have y⁻¹ * x ∈ H, from inv_mul_mem_of_lcoset_eq_lcoset hyp₀,
  eq.symm (eq_of_inv_mul_mem_ker (hyp₁ this))

  variables (H f)
  proposition subset_ker_iff : H ⊆ ker f ↔ ∀ x y, x * H = y * H → f x = f y :=
  iff.intro (λ h₁ x y h₀, eq_of_lcoset_eq_lcoset_of_subset_ker h₀ h₁) subset_ker_of_forall
end subgroupH

section subgroupGH
  variables [group A] [group B] {G H : set A} [is_subgroup G] [is_subgroup H]
  variables {f : A → B} [is_hom_on f G]

  proposition subset_ker_in_of_forall (hyp₀ : ∀₀ x ∈ G, ∀₀ y ∈ G, x * H = y * H → f x = f y)
      (hyp₁ : H ⊆ G) :
    H ⊆ ker_in f G :=
  take h, assume hH,
    have hG : h ∈ G, from hyp₁ hH,
    and.intro
      (have h * H = 1 * H, by rewrite [lcoset_eq_self_of_mem hH, one_lcoset],
        have f h = f 1, from hyp₀ hG one_mem this,
        show f h = 1, by rewrite [this, hom_on_one f G])
      hG

  proposition eq_of_lcoset_eq_lcoset_of_subset_ker_in {x : A} (xG : x ∈ G) {y : A} (yG : y ∈ G)
      (hyp₀ : x * H = y * H) (hyp₁ : H ⊆ ker_in f G) :
    f x = f y :=
  have y⁻¹ * x ∈ H, from inv_mul_mem_of_lcoset_eq_lcoset hyp₀,
  eq.symm (eq_of_inv_mul_mem_ker_in yG xG (hyp₁ this))

  variables (H f)
  proposition subset_ker_in_iff :
    H ⊆ ker_in f G ↔ (H ⊆ G ∧ ∀₀ x ∈ G, ∀₀ y ∈ G, x * H = y * H → f x = f y) :=
  iff.intro
    (λ h₁, and.intro
      (subset.trans h₁ (inter_subset_right _ _))
      (λ x xG y yG h₀, eq_of_lcoset_eq_lcoset_of_subset_ker_in xG yG h₀ h₁))
    (λ h, subset_ker_in_of_forall (and.right h) (and.left h))
end subgroupGH


/- the centralizer -/

section has_mulA
  variable [has_mul A]

  abbreviation centralizes [reducible] (a : A) (S : set A) : Prop := ∀₀ b ∈ S, a * b = b * a

  definition centralizer (S : set A) : set A := { a : A | centralizes a S }

  abbreviation is_centralized_by (S T : set A) : Prop := T ⊆ centralizer S

  abbreviation centralizer_in (S T : set A) : set A := T ∩ centralizer S

  proposition mem_centralizer_iff_centralizes (a : A) (S : set A) :
    a ∈ centralizer S ↔ centralizes a S := iff.refl _

  proposition normalizes_of_centralizes {a : A} {S : set A} (H : centralizes a S) :
    normalizes a S :=
  ext (take b, iff.intro
    (suppose b ∈ a * S,
      obtain s [ains (beq : a * s = b)], from this,
      show b ∈ S * a, by rewrite[-beq, H ains]; apply mem_image_of_mem _ ains)
    (suppose b ∈ S * a,
      obtain s [ains (beq : s * a = b)], from this,
      show b ∈ a * S, by rewrite[-beq, -H ains]; apply mem_image_of_mem _ ains))

  proposition centralizer_subset_normalizer (S : set A) : centralizer S ⊆ normalizer S :=
  λ a acent, normalizes_of_centralizes acent

  proposition centralizer_subset_centralizer {S T : set A} (ssubt : S ⊆ T) :
    centralizer T ⊆ centralizer S :=
  λ x xCentT s sS, xCentT _ (ssubt sS)
end has_mulA

section groupA
  variable [group A]

  proposition is_subgroup_centralizer [instance] [group A] (S : set A) :
    is_subgroup (centralizer S) :=
  ⦃ is_subgroup,
    one_mem := λ b bS, by rewrite [one_mul, mul_one],
    mul_mem := λ a acent b bcent c cS, by rewrite [mul.assoc, bcent cS, -*mul.assoc, acent cS],
    inv_mem := λ a acent c cS, eq_mul_inv_of_mul_eq
      (by rewrite [mul.assoc, -acent cS, inv_mul_cancel_left])⦄
end groupA


/- the subgroup generated by a set -/

section groupA
  variable [group A]

  inductive subgroup_generated_by (S : set A) : A → Prop :=
  | generators_mem : ∀ x, x ∈ S → subgroup_generated_by S x
  | one_mem        : subgroup_generated_by S 1
  | mul_mem        : ∀ x y, subgroup_generated_by S x → subgroup_generated_by S y →
                       subgroup_generated_by S (x * y)
  | inv_mem        : ∀ x, subgroup_generated_by S x → subgroup_generated_by S (x⁻¹)

  theorem generators_subset_subgroup_generated_by (S : set A) : S ⊆ subgroup_generated_by S :=
  subgroup_generated_by.generators_mem

  theorem is_subgroup_subgroup_generated_by [instance] (S : set A) :
    is_subgroup (subgroup_generated_by S) :=
  ⦃ is_subgroup,
    one_mem := subgroup_generated_by.one_mem S,
    mul_mem := λ a amem b bmem, subgroup_generated_by.mul_mem a b amem bmem,
    inv_mem := λ a amem, subgroup_generated_by.inv_mem a amem ⦄

  theorem subgroup_generated_by_subset {S G : set A} [is_subgroup G] (H : S ⊆ G) :
    subgroup_generated_by S ⊆ G :=
  begin
    intro x xgenS,
    induction xgenS with a aS a b agen bgen aG bG a agen aG,
      {exact H aS},
      {exact one_mem},
      {exact mul_mem aG bG},
    exact inv_mem aG
  end
end groupA

end group_theory
