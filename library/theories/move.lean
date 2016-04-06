/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Temporary file; move in Lean3.
-/
import data.set algebra.order_bigops
import data.finset data.list.sort

-- move to data.set

namespace set

lemma inter_eq_self_of_subset {X : Type} {s t : set X} (Hst : s ⊆ t) : s ∩ t = s :=
ext (take x, iff.intro
  (assume H, !inter_subset_left H)
  (assume H, and.intro H (Hst H)))

lemma inter_eq_self_of_subset_right {X : Type} {s t : set X} (Hst : t ⊆ s) : s ∩ t = t :=
by rewrite [inter_comm]; apply inter_eq_self_of_subset Hst

proposition diff_self_inter {X : Type} (s t : set X) : s \ (s ∩ t) = s \ t :=
by rewrite [*diff_eq, compl_inter, inter_distrib_left, inter_compl_self, empty_union]

proposition diff_eq_diff {X : Type} {s t u : set X} (H : s ∩ u = s ∩ t) :
  s \ u = s \ t :=
by rewrite [-diff_self_inter, H, diff_self_inter]

-- classical
proposition inter_eq_inter_of_diff_eq_diff {X : Type} {s t u : set X} (H : s \ u = s \ t) :
  s ∩ u = s ∩ t :=
by rewrite [-compl_compl u, -compl_compl t]; apply diff_eq_diff H

proposition compl_inter_eq_compl_inter {X : Type} {s t u : set X}
    (H : u ∩ s = t ∩ s) :
  -u ∩ s = -t ∩ s :=
by rewrite [*inter_comm _ s]; apply diff_eq_diff; rewrite [*inter_comm s, H]

proposition inter_eq_inter_of_compl_inter_eq_compl_inter {X : Type} {s t u : set X}
    (H : -u ∩ s = -t ∩ s) :
  u ∩ s = t ∩ s :=
begin
  rewrite [*inter_comm _ s], apply inter_eq_inter_of_diff_eq_diff,
  rewrite [*diff_eq, *inter_comm s, H]
end

proposition singleton_subset_of_mem {X : Type} {x : X} {s : set X} (xs : x ∈ s) : '{x} ⊆ s :=
take y, assume yx,
  have y = x, from eq_of_mem_singleton yx,
  by rewrite this; exact xs

proposition mem_of_singleton_subset {X : Type} {x : X} {s : set X} (xs : '{x} ⊆ s) : x ∈ s :=
xs !mem_singleton

proposition singleton_subset_iff {X : Type} (x : X) (s : set X) : '{x} ⊆ s ↔ x ∈ s :=
iff.intro mem_of_singleton_subset singleton_subset_of_mem

lemma inter_eq_inter_left {X : Type} {s t u : set X} (H₁ : s ∩ t ⊆ u) (H₂ : s ∩ u ⊆ t) :
  s ∩ t = s ∩ u :=
eq_of_subset_of_subset
  (subset_inter (inter_subset_left _ _) H₁)
  (subset_inter (inter_subset_left _ _) H₂)

lemma inter_eq_inter_right {X : Type} {s t u : set X} (H₁ : s ∩ t ⊆ u) (H₂ : u ∩ t ⊆ s) :
  s ∩ t = u ∩ t :=
eq_of_subset_of_subset
  (subset_inter H₁ (inter_subset_right _ _))
  (subset_inter H₂ (inter_subset_right _ _))

proposition sUnion_subset {X : Type} {S : set (set X)} {t : set X} (H : ∀₀ u ∈ S, u ⊆ t) :
  ⋃₀ S ⊆ t :=
take x, assume Hx,
obtain u [uS xu], from Hx,
H uS xu

proposition subset_of_sUnion_subset {X : Type} {S : set (set X)} {t : set X}
  (H : ⋃₀ S ⊆ t) {u : set X} (Hu : u ∈ S) : u ⊆ t :=
λ x xu, H (exists.intro u (and.intro Hu xu))

proposition preimage_Union {I X Y : Type} (f : X → Y) (u : I → set Y) :
  f '- (⋃ i, u i) = ⋃ i, (f '- (u i)) :=
ext (take x, !iff.refl)

lemma finite_sUnion {A : Type} {S : set (set A)} [H : finite S] :
  (∀s, s ∈ S → finite s) → finite ⋃₀S :=
induction_on_finite S
  (by intro H; rewrite sUnion_empty; apply finite_empty)
  (take a s, assume fins anins ih h,
    begin
      rewrite sUnion_insert,
      apply finite_union,
        {apply h _ (mem_insert a s)},
      apply ih (forall_of_forall_insert h)
    end)

lemma subset_powerset_sUnion {A : Type} (S : set (set A)) : S ⊆ 𝒫 (⋃₀ S) :=
take u, suppose u ∈ S, show u ⊆ ⋃₀ S, from subset_sUnion_of_mem this

lemma finite_of_finite_sUnion {A : Type} (S : set (set A)) (H : finite ⋃₀S) : finite S :=
have finite (𝒫 (⋃₀ S)), from finite_powerset _,
show finite S, from finite_subset (subset_powerset_sUnion S)

end set


-- move to data.finset

namespace finset

section
  variables {A : Type} [decidable_linear_order A]

  definition finset_to_list (s : finset A) : list A :=
  quot.lift_on s
    (take l, list.sort le (subtype.elt_of l))
    (take a b, assume eqab, list.sort_eq_of_perm eqab)

  proposition to_finset_finset_to_list (s : finset A) : to_finset (finset_to_list s) = s :=
  quot.induction_on s
    begin
      intro l,
      have H : list.nodup (list.sort le (subtype.elt_of l)),
        from perm.nodup_of_perm_of_nodup (perm.symm !list.sort_perm) (subtype.has_property l),
      rewrite [↑finset_to_list, -to_finset_eq_of_nodup H],
      apply quot.sound,
      apply list.sort_perm
    end

  proposition nodup_finset_to_list (s : finset A) : list.nodup (finset_to_list s) :=
  quot.induction_on s
    (take l, perm.nodup_of_perm_of_nodup (perm.symm !list.sort_perm) (subtype.has_property l))

  proposition sorted_finset_to_list (s : finset A) : list.sorted le (finset_to_list s) :=
  quot.induction_on s
    (take l, list.sorted_of_strongly_sorted (list.strongly_sorted_sort _))
end

end finset


-- move to data.nat?

namespace nat
open finset

theorem succ_Max₀_not_mem (s : finset ℕ) : succ (Max₀ s) ∉ s :=
suppose succ (Max₀ s) ∈ s,
have succ (Max₀ s) ≤ Max₀ s, from le_Max₀ this,
show false, from not_succ_le_self this

end nat
