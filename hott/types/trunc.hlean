/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Properties of trunc_index, is_trunc, trunctype, trunc, and the pointed versions of these
-/

-- NOTE: the fact that (is_trunc n A) is a mere proposition is proved in .prop_trunc

import .pointed ..function algebra.order types.nat.order

open eq sigma sigma.ops pi function equiv trunctype
     is_equiv prod pointed nat is_trunc algebra sum

  /- basic computation with ℕ₋₂, its operations and its order -/
namespace trunc_index

  definition minus_one_le_succ (n : ℕ₋₂) : -1 ≤ n.+1 :=
  succ_le_succ (minus_two_le n)

  definition zero_le_of_nat (n : ℕ) : 0 ≤ of_nat n :=
  succ_le_succ !minus_one_le_succ

  open decidable
  protected definition has_decidable_eq [instance] : Π(n m : ℕ₋₂), decidable (n = m)
  | has_decidable_eq -2     -2     := inl rfl
  | has_decidable_eq (n.+1) -2     := inr (by contradiction)
  | has_decidable_eq -2     (m.+1) := inr (by contradiction)
  | has_decidable_eq (n.+1) (m.+1) :=
      match has_decidable_eq n m with
      | inl xeqy := inl (by rewrite xeqy)
      | inr xney := inr (λ h : succ n = succ m, by injection h with xeqy; exact absurd xeqy xney)
      end

  definition not_succ_le_minus_two {n : ℕ₋₂} (H : n .+1 ≤ -2) : empty :=
  by cases H

  protected definition le_trans {n m k : ℕ₋₂} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k :=
  begin
    induction H2 with k H2 IH,
    { exact H1},
    { exact le.step IH}
  end

  definition le_of_succ_le_succ {n m : ℕ₋₂} (H : n.+1 ≤ m.+1) : n ≤ m :=
  begin
    cases H with m H',
    { apply le.tr_refl},
    { exact trunc_index.le_trans (le.step !le.tr_refl) H'}
  end

  theorem not_succ_le_self {n : ℕ₋₂} : ¬n.+1 ≤ n :=
  begin
    induction n with n IH: intro H,
    { exact not_succ_le_minus_two H},
    { exact IH (le_of_succ_le_succ H)}
  end

  protected definition le_antisymm {n m : ℕ₋₂} (H1 : n ≤ m) (H2 : m ≤ n) : n = m :=
  begin
    induction H2 with n H2 IH,
    { reflexivity},
    { exfalso, apply @not_succ_le_self n, exact trunc_index.le_trans H1 H2}
  end

  protected definition le_succ {n m : ℕ₋₂} (H1 : n ≤ m) : n ≤ m.+1 :=
  le.step H1

  protected definition self_le_succ (n : ℕ₋₂) : n ≤ n.+1 :=
  le.step (trunc_index.le.tr_refl n)

  -- the order is total
  protected theorem le_sum_le (n m : ℕ₋₂) : n ≤ m ⊎ m ≤ n :=
  begin
    induction m with m IH,
    { exact inr !minus_two_le},
    { cases IH with H H,
      { exact inl (trunc_index.le_succ H)},
      { cases H with n' H,
        { exact inl !trunc_index.self_le_succ},
        { exact inr (succ_le_succ H)}}}
  end

end trunc_index open trunc_index

definition linear_weak_order_trunc_index [trans_instance] [reducible] :
  linear_weak_order trunc_index :=
linear_weak_order.mk le trunc_index.le.tr_refl @trunc_index.le_trans @trunc_index.le_antisymm
                     trunc_index.le_sum_le

namespace trunc_index

  /- more theorems about truncation indices -/

  definition zero_add (n : ℕ₋₂) : (0 : ℕ₋₂) + n = n :=
  begin
    cases n with n, reflexivity,
    cases n with n, reflexivity,
    induction n with n IH, reflexivity, exact ap succ IH
  end

  definition add_zero (n : ℕ₋₂) : n + (0 : ℕ₋₂) = n :=
  by reflexivity

  definition succ_add_nat (n : ℕ₋₂) (m : ℕ) : n.+1 + m = (n + m).+1 :=
  by induction m with m IH; reflexivity; exact ap succ IH

  definition nat_add_succ (n : ℕ) (m : ℕ₋₂) : n + m.+1 = (n + m).+1 :=
  begin
    cases m with m, reflexivity,
    cases m with m, reflexivity,
    induction m with m IH, reflexivity, exact ap succ IH
  end

  definition add_nat_succ (n : ℕ₋₂) (m : ℕ) : n + (nat.succ m) = (n + m).+1 :=
  by reflexivity

  definition nat_succ_add (n : ℕ) (m : ℕ₋₂) : (nat.succ n) + m = (n + m).+1 :=
  begin
    cases m with m, reflexivity,
    cases m with m, reflexivity,
    induction m with m IH, reflexivity, exact ap succ IH
  end

  definition sub_two_add_two (n : ℕ₋₂) : sub_two (add_two n) = n :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap succ IH}
  end

  definition add_two_sub_two (n : ℕ) : add_two (sub_two n) = n :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap nat.succ IH}
  end

  definition of_nat_add_plus_two_of_nat (n m : ℕ) : n +2+ m = of_nat (n + m + 2) :=
  begin
    induction m with m IH,
    { reflexivity},
    { exact ap succ IH}
  end

  definition of_nat_add_of_nat (n m : ℕ) : of_nat n + of_nat m = of_nat (n + m) :=
  begin
    induction m with m IH,
    { reflexivity},
    { exact ap succ IH}
  end

  definition succ_add_plus_two (n m : ℕ₋₂) : n.+1 +2+ m = (n +2+ m).+1 :=
  begin
    induction m with m IH,
    { reflexivity},
    { exact ap succ IH}
  end

  definition add_plus_two_succ (n m : ℕ₋₂) : n +2+ m.+1 = (n +2+ m).+1 :=
  idp

  definition add_succ_succ (n m : ℕ₋₂) : n + m.+2 = n +2+ m :=
  idp

  definition succ_add_succ (n m : ℕ₋₂) : n.+1 + m.+1 = n +2+ m :=
  begin
    cases m with m IH,
    { reflexivity},
    { apply succ_add_plus_two}
  end

  definition succ_succ_add (n m : ℕ₋₂) : n.+2 + m = n +2+ m :=
  begin
    cases m with m IH,
    { reflexivity},
    { exact !succ_add_succ ⬝ !succ_add_plus_two}
  end

  definition succ_sub_two (n : ℕ) : (nat.succ n).-2 = n.-2 .+1 := rfl
  definition sub_two_succ_succ (n : ℕ) : n.-2.+1.+1 = n := rfl
  definition succ_sub_two_succ (n : ℕ) : (nat.succ n).-2.+1 = n := rfl

  definition of_nat_add_two (n : ℕ₋₂) : of_nat (add_two n) = n.+2 :=
  begin induction n with n IH, reflexivity, exact ap succ IH end

  definition of_nat_le_of_nat {n m : ℕ} (H : n ≤ m) : (of_nat n ≤ of_nat m) :=
  begin
    induction H with m H IH,
    { apply le.refl},
    { exact trunc_index.le_succ IH}
  end

  definition sub_two_le_sub_two {n m : ℕ} (H : n ≤ m) : n.-2 ≤ m.-2 :=
  begin
    induction H with m H IH,
    { apply le.refl},
    { exact trunc_index.le_succ IH}
  end

  definition add_two_le_add_two {n m : ℕ₋₂} (H : n ≤ m) : add_two n ≤ add_two m :=
  begin
    induction H with m H IH,
    { reflexivity},
    { constructor, exact IH},
  end

  definition le_of_sub_two_le_sub_two {n m : ℕ} (H : n.-2 ≤ m.-2) : n ≤ m :=
  begin
    rewrite [-add_two_sub_two n, -add_two_sub_two m],
    exact add_two_le_add_two H,
  end

  definition le_of_of_nat_le_of_nat {n m : ℕ} (H : of_nat n ≤ of_nat m) : n ≤ m :=
  begin
    apply le_of_sub_two_le_sub_two,
    exact le_of_succ_le_succ (le_of_succ_le_succ H)
  end

  protected theorem succ_le_of_not_le {n m : ℕ₋₂} (H : ¬ n ≤ m) : m.+1 ≤ n :=
  begin
    cases (le.total n m) with H2 H2,
    { exfalso, exact H H2},
    { cases H2 with n' H2',
      { exfalso, exact H !le.refl},
      { exact succ_le_succ H2'}}
  end

  definition trunc_index.decidable_le [instance] : Π(n m : ℕ₋₂), decidable (n ≤ m) :=
  begin
    intro n, induction n with n IH: intro m,
    { left, apply minus_two_le},
    cases m with m,
    { right, apply not_succ_le_minus_two},
    cases IH m with H H,
    { left, apply succ_le_succ H},
    right, intro H2, apply H, exact le_of_succ_le_succ H2
  end

end trunc_index open trunc_index

namespace is_trunc

  variables {A B : Type} {n : ℕ₋₂}

  /- closure properties of truncatedness -/
  theorem is_trunc_is_embedding_closed (f : A → B) [Hf : is_embedding f] [HB : is_trunc n B]
    (Hn : -1 ≤ n) : is_trunc n A :=
  begin
    induction n with n,
      {exfalso, exact not_succ_le_minus_two Hn},
      {apply is_trunc_succ_intro, intro a a',
         fapply @is_trunc_is_equiv_closed_rev _ _ n (ap f)}
  end

  theorem is_trunc_is_retraction_closed (f : A → B) [Hf : is_retraction f]
    (n : ℕ₋₂) [HA : is_trunc n A] : is_trunc n B :=
  begin
    revert A B f Hf HA,
    induction n with n IH,
    { intro A B f Hf HA, induction Hf with g ε, fapply is_contr.mk,
      { exact f (center A)},
      { intro b, apply concat,
        { apply (ap f), exact (center_eq (g b))},
        { apply ε}}},
    { intro A B f Hf HA, induction Hf with g ε,
      apply is_trunc_succ_intro, intro b b',
      fapply (IH (g b = g b')),
      { intro q, exact ((ε b)⁻¹ ⬝ ap f q ⬝ ε b')},
      { apply (is_retraction.mk (ap g)),
        { intro p, induction p, {rewrite [↑ap, con.left_inv]}}},
      { apply is_trunc_eq}}
  end

  definition is_embedding_to_fun (A B : Type) : is_embedding (@to_fun A B)  :=
  λf f', !is_equiv_ap_to_fun

  /- theorems about trunctype -/
  protected definition trunctype.sigma_char.{l} [constructor] (n : ℕ₋₂) :
    (trunctype.{l} n) ≃ (Σ (A : Type.{l}), is_trunc n A) :=
  begin
    fapply equiv.MK,
    { intro A, exact (⟨carrier A, struct A⟩)},
    { intro S, exact (trunctype.mk S.1 S.2)},
    { intro S, induction S with S1 S2, reflexivity},
    { intro A, induction A with A1 A2, reflexivity},
  end

  definition trunctype_eq_equiv [constructor] (n : ℕ₋₂) (A B : n-Type) :
    (A = B) ≃ (carrier A = carrier B) :=
  calc
    (A = B) ≃ (to_fun (trunctype.sigma_char n) A = to_fun (trunctype.sigma_char n) B)
              : eq_equiv_fn_eq_of_equiv
      ... ≃ ((to_fun (trunctype.sigma_char n) A).1 = (to_fun (trunctype.sigma_char n) B).1)
             : equiv.symm (!equiv_subtype)
      ... ≃ (carrier A = carrier B) : equiv.refl

  theorem is_trunc_trunctype [instance] (n : ℕ₋₂) : is_trunc n.+1 (n-Type) :=
  begin
    apply is_trunc_succ_intro, intro X Y,
    fapply is_trunc_equiv_closed_rev, { apply trunctype_eq_equiv},
    fapply is_trunc_equiv_closed_rev, { apply eq_equiv_equiv},
    induction n,
    { apply @is_contr_of_inhabited_prop,
      { apply is_trunc_is_embedding_closed,
        { apply is_embedding_to_fun} ,
        { reflexivity}},
      { apply equiv_of_is_contr_of_is_contr}},
    { apply is_trunc_is_embedding_closed,
      { apply is_embedding_to_fun},
      { apply minus_one_le_succ}}
  end

  /- univalence for truncated types -/
  definition teq_equiv_equiv {n : ℕ₋₂} {A B : n-Type} : (A = B) ≃ (A ≃ B) :=
  trunctype_eq_equiv n A B ⬝e eq_equiv_equiv A B

  definition tua {n : ℕ₋₂} {A B : n-Type} (f : A ≃ B) : A = B :=
  (trunctype_eq_equiv n A B)⁻¹ᶠ (ua f)

  definition tua_refl {n : ℕ₋₂} (A : n-Type) : tua (@erfl A) = idp :=
  begin
    refine ap (trunctype_eq_equiv n A A)⁻¹ᶠ (ua_refl A) ⬝ _,
    refine ap (eq_of_fn_eq_fn _) _ ⬝ !eq_of_fn_eq_fn'_idp ,
    apply ap (dpair_eq_dpair idp), apply is_prop.elim
  end

  definition tua_trans {n : ℕ₋₂} {A B C : n-Type} (f : A ≃ B) (g : B ≃ C)
    : tua (f ⬝e g) = tua f ⬝ tua g :=
  begin
    refine ap (trunctype_eq_equiv n A C)⁻¹ᶠ (ua_trans f g) ⬝ _,
    refine ap (eq_of_fn_eq_fn _) _ ⬝ !eq_of_fn_eq_fn'_con,
    refine _ ⬝ !dpair_eq_dpair_con,
    apply ap (dpair_eq_dpair _), esimp, apply is_prop.elim
  end

  definition tua_symm {n : ℕ₋₂} {A B : n-Type} (f : A ≃ B) : tua f⁻¹ᵉ = (tua f)⁻¹ :=
  begin
    apply eq_inv_of_con_eq_idp',
    refine !tua_trans⁻¹ ⬝ _,
    refine ap tua _ ⬝ !tua_refl,
    apply equiv_eq, exact to_right_inv f
  end

  definition tcast [unfold 4] {n : ℕ₋₂} {A B : n-Type} (p : A = B) (a : A) : B :=
  cast (ap trunctype.carrier p) a

  definition ptcast [constructor] {n : ℕ₋₂} {A B : n-Type*} (p : A = B) : A →* B :=
  pcast (ap ptrunctype.to_pType p)

  theorem tcast_tua_fn {n : ℕ₋₂} {A B : n-Type} (f : A ≃ B) : tcast (tua f) = to_fun f :=
  begin
    cases A with A HA, cases B with B HB, esimp at *,
    induction f using rec_on_ua_idp, esimp,
    have HA = HB, from !is_prop.elim, cases this,
    exact ap tcast !tua_refl
  end

  /- theorems about decidable equality and axiom K -/
  theorem is_set_of_axiom_K {A : Type} (K : Π{a : A} (p : a = a), p = idp) : is_set A :=
  is_set.mk _ (λa b p q, eq.rec K q p)

  theorem is_set_of_relation.{u} {A : Type.{u}} (R : A → A → Type.{u})
    (mere : Π(a b : A), is_prop (R a b)) (refl : Π(a : A), R a a)
    (imp : Π{a b : A}, R a b → a = b) : is_set A :=
  is_set_of_axiom_K
    (λa p,
      have H2 : transport (λx, R a x → a = x) p (@imp a a) = @imp a a, from !apdt,
      have H3 : Π(r : R a a), transport (λx, a = x) p (imp r)
                              = imp (transport (λx, R a x) p r), from
        to_fun (equiv.symm !heq_pi) H2,
      have H4 : imp (refl a) ⬝ p = imp (refl a), from
        calc
          imp (refl a) ⬝ p = transport (λx, a = x) p (imp (refl a)) : eq_transport_r
            ... = imp (transport (λx, R a x) p (refl a)) : H3
            ... = imp (refl a) : is_prop.elim,
      cancel_left (imp (refl a)) H4)

  definition relation_equiv_eq {A : Type} (R : A → A → Type)
    (mere : Π(a b : A), is_prop (R a b)) (refl : Π(a : A), R a a)
    (imp : Π{a b : A}, R a b → a = b) (a b : A) : R a b ≃ a = b :=
  have is_set A, from is_set_of_relation R mere refl @imp,
  equiv_of_is_prop imp (λp, p ▸ refl a)

  local attribute not [reducible]
  theorem is_set_of_double_neg_elim {A : Type} (H : Π(a b : A), ¬¬a = b → a = b)
    : is_set A :=
  is_set_of_relation (λa b, ¬¬a = b) _ (λa n, n idp) H

  section
  open decidable
  --this is proven differently in init.hedberg
  theorem is_set_of_decidable_eq (A : Type) [H : decidable_eq A] : is_set A :=
  is_set_of_double_neg_elim (λa b, by_contradiction)
  end

  theorem is_trunc_of_axiom_K_of_le {A : Type} {n : ℕ₋₂} (H : -1 ≤ n)
    (K : Π(a : A), is_trunc n (a = a)) : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λa b, is_trunc_of_imp_is_trunc_of_le H (λp, eq.rec_on p !K))

  theorem is_trunc_succ_of_is_trunc_loop (Hn : -1 ≤ n) (Hp : Π(a : A), is_trunc n (a = a))
    : is_trunc (n.+1) A :=
  begin
    apply is_trunc_succ_intro, intros a a',
    apply is_trunc_of_imp_is_trunc_of_le Hn, intro p,
    induction p, apply Hp
  end

  theorem is_prop_iff_is_contr {A : Type} (a : A) :
    is_prop A ↔ is_contr A :=
  iff.intro (λH, is_contr.mk a (is_prop.elim a)) _

  theorem is_trunc_succ_iff_is_trunc_loop (A : Type) (Hn : -1 ≤ n) :
    is_trunc (n.+1) A ↔ Π(a : A), is_trunc n (a = a) :=
  iff.intro _ (is_trunc_succ_of_is_trunc_loop Hn)

  -- use loopn in name
  theorem is_trunc_iff_is_contr_loop_succ (n : ℕ) (A : Type)
    : is_trunc n A ↔ Π(a : A), is_contr (Ω[succ n](pointed.Mk a)) :=
  begin
    revert A, induction n with n IH,
    { intro A, esimp [loopn], transitivity _,
      { apply is_trunc_succ_iff_is_trunc_loop, apply le.refl},
      { apply pi_iff_pi, intro a, esimp, apply is_prop_iff_is_contr, reflexivity}},
    { intro A, esimp [loopn],
      transitivity _,
      { apply @is_trunc_succ_iff_is_trunc_loop @n, esimp, apply minus_one_le_succ},
      apply pi_iff_pi, intro a, transitivity _, apply IH,
      transitivity _, apply pi_iff_pi, intro p,
      rewrite [loopn_space_loop_irrel n p], apply iff.refl, esimp,
      apply imp_iff, reflexivity}
  end

  -- use loopn in name
  theorem is_trunc_iff_is_contr_loop (n : ℕ) (A : Type)
    : is_trunc (n.-2.+1) A ↔ (Π(a : A), is_contr (Ω[n](pointed.Mk a))) :=
  begin
    induction n with n,
    { esimp [sub_two,loopn], apply iff.intro,
        intro H a, exact is_contr_of_inhabited_prop a,
        intro H, apply is_prop_of_imp_is_contr, exact H},
    { apply is_trunc_iff_is_contr_loop_succ},
  end

  -- rename to is_contr_loopn_of_is_trunc
  theorem is_contr_loop_of_is_trunc (n : ℕ) (A : Type*) [H : is_trunc (n.-2.+1) A] :
    is_contr (Ω[n] A) :=
  begin
    induction A,
    apply iff.mp !is_trunc_iff_is_contr_loop H
  end

  -- rename to is_trunc_loopn_of_is_trunc
  theorem is_trunc_loop_of_is_trunc (n : ℕ₋₂) (k : ℕ) (A : Type*) [H : is_trunc n A] :
    is_trunc n (Ω[k] A) :=
  begin
    induction k with k IH,
    { exact H},
    { apply is_trunc_eq}
  end

  definition is_trunc_loopn (k : ℕ₋₂) (n : ℕ) (A : Type*) [H : is_trunc (k+n) A]
    : is_trunc k (Ω[n] A) :=
  begin
    revert k H, induction n with n IH: intro k H, exact _,
    apply is_trunc_eq, apply IH, rewrite [succ_add_nat, add_nat_succ at H], exact H
  end

  definition is_set_loopn (n : ℕ) (A : Type*) [is_trunc n A] : is_set (Ω[n] A) :=
  have is_trunc (0+[ℕ₋₂]n) A, by rewrite [trunc_index.zero_add]; exact _,
  is_trunc_loopn 0 n A

end is_trunc open is_trunc

namespace trunc
  universe variable u
  variables {n : ℕ₋₂} {A : Type.{u}} {B : Type} {a₁ a₂ a₃ a₄ : A}

  definition trunc_functor2 [unfold 6 7] {n : ℕ₋₂} {A B C : Type} (f : A → B → C)
    (x : trunc n A) (y : trunc n B) : trunc n C :=
  by induction x with a; induction y with b; exact tr (f a b)

  definition tconcat [unfold 6 7] (p : trunc n (a₁ = a₂)) (q : trunc n (a₂ = a₃)) :
    trunc n (a₁ = a₃) :=
  trunc_functor2 concat p q

  definition tinverse [unfold 5] (p : trunc n (a₁ = a₂)) : trunc n (a₂ = a₁) :=
  trunc_functor _ inverse p

  definition tidp [reducible] [constructor] : trunc n (a₁ = a₁) :=
  tr idp

  definition tassoc (p : trunc n (a₁ = a₂)) (q : trunc n (a₂ = a₃))
    (r : trunc n (a₃ = a₄)) : tconcat (tconcat p q) r = tconcat p (tconcat q r) :=
  by induction p; induction q; induction r; exact ap tr !con.assoc

  definition tidp_tcon (p : trunc n (a₁ = a₂)) : tconcat tidp p = p :=
  by induction p; exact ap tr !idp_con

  definition tcon_tidp (p : trunc n (a₁ = a₂)) : tconcat p tidp = p :=
  by induction p; reflexivity

  definition left_tinv (p : trunc n (a₁ = a₂)) : tconcat (tinverse p) p = tidp :=
  by induction p; exact ap tr !con.left_inv

  definition right_tinv (p : trunc n (a₁ = a₂)) : tconcat p (tinverse p) = tidp :=
  by induction p; exact ap tr !con.right_inv

  definition tap [unfold 7] (f : A → B) (p : trunc n (a₁ = a₂)) : trunc n (f a₁ = f a₂) :=
  trunc_functor _ (ap f) p

  definition tap_tidp (f : A → B) : tap f (@tidp n A a₁) = tidp := idp
  definition tap_tcon (f : A → B) (p : trunc n (a₁ = a₂)) (q : trunc n (a₂ = a₃)) :
    tap f (tconcat p q) = tconcat (tap f p) (tap f q) :=
  by induction p; induction q; exact ap tr !ap_con

  /- characterization of equality in truncated types -/
  protected definition code [unfold 3 4] (n : ℕ₋₂) (aa aa' : trunc n.+1 A) : trunctype.{u} n :=
  by induction aa with a; induction aa' with a'; exact trunctype.mk' n (trunc n (a = a'))

  protected definition encode [unfold 3 5] {n : ℕ₋₂} {aa aa' : trunc n.+1 A}
    : aa = aa' → trunc.code n aa aa' :=
  begin
    intro p, induction p, induction aa with a, esimp, exact (tr idp)
  end

  protected definition decode [unfold 3 4 5] {n : ℕ₋₂} (aa aa' : trunc n.+1 A) :
    trunc.code n aa aa' → aa = aa' :=
  begin
    induction aa' with a', induction aa with a,
    esimp [trunc.code, trunc.rec_on], intro x,
    induction x with p, exact ap tr p,
  end

  definition trunc_eq_equiv [constructor] (n : ℕ₋₂) (aa aa' : trunc n.+1 A)
    : aa = aa' ≃ trunc.code n aa aa' :=
  begin
    fapply equiv.MK,
    { apply trunc.encode},
    { apply trunc.decode},
    { eapply (trunc.rec_on aa'), eapply (trunc.rec_on aa),
      intro a a' x, esimp [trunc.code, trunc.rec_on] at x,
      refine (@trunc.rec_on n _ _ x _ _),
        intro x, apply is_trunc_eq,
        intro p, induction p, reflexivity},
    { intro p, induction p, apply (trunc.rec_on aa), intro a, exact idp},
  end

  definition tr_eq_tr_equiv [constructor] (n : ℕ₋₂) (a a' : A)
    : (tr a = tr a' :> trunc n.+1 A) ≃ trunc n (a = a') :=
  !trunc_eq_equiv

  definition code_mul {n : ℕ₋₂} {aa₁ aa₂ aa₃ : trunc n.+1 A}
    (g : trunc.code n aa₁ aa₂) (h : trunc.code n aa₂ aa₃) : trunc.code n aa₁ aa₃ :=
  begin
    induction aa₁ with a₁, induction aa₂ with a₂, induction aa₃ with a₃,
    esimp at *, apply tconcat g h,
  end

  /- encode preserves concatenation -/
  definition encode_con' {n : ℕ₋₂} {aa₁ aa₂ aa₃ : trunc n.+1 A} (p : aa₁ = aa₂) (q : aa₂ = aa₃)
    : trunc.encode (p ⬝ q) = code_mul (trunc.encode p) (trunc.encode q) :=
  begin
    induction p, induction q, induction aa₁ with a₁, reflexivity
  end

  definition encode_con {n : ℕ₋₂} {a₁ a₂ a₃ : A} (p : tr a₁ = tr a₂ :> trunc (n.+1) A)
    (q : tr a₂ = tr a₃ :> trunc (n.+1) A)
    : trunc.encode (p ⬝ q) = tconcat (trunc.encode p) (trunc.encode q) :=
  encode_con' p q

  /- the principle of unique choice -/
  definition unique_choice {P : A → Type} [H : Πa, is_prop (P a)] (f : Πa, ∥ P a ∥) (a : A)
    : P a :=
  !trunc_equiv (f a)

  /- transport over a truncated family -/
  definition trunc_transport {a a' : A} {P : A → Type} (p : a = a') (n : ℕ₋₂) (x : P a)
    : transport (λa, trunc n (P a)) p (tr x) = tr (p ▸ x) :=
  by induction p; reflexivity

  /- pathover over a truncated family -/
  definition trunc_pathover {A : Type} {B : A → Type} {n : ℕ₋₂} {a a' : A} {p : a = a'}
    {b : B a} {b' : B a'} (q : b =[p] b') : @tr n _ b =[p] @tr n _ b' :=
  by induction q; constructor

  /- truncations preserve truncatedness -/
  definition is_trunc_trunc_of_is_trunc [instance] [priority 500] (A : Type)
    (n m : ℕ₋₂) [H : is_trunc n A] : is_trunc n (trunc m A) :=
  begin
    revert A m H, eapply (trunc_index.rec_on n),
    { clear n, intro A m H, apply is_contr_equiv_closed,
      { apply equiv.symm, apply trunc_equiv, apply (@is_trunc_of_le _ -2), apply minus_two_le} },
    { clear n, intro n IH A m H, induction m with m,
      { apply (@is_trunc_of_le _ -2), apply minus_two_le},
      { apply is_trunc_succ_intro, intro aa aa',
        apply (@trunc.rec_on _ _ _ aa  (λy, !is_trunc_succ_of_is_prop)),
        eapply (@trunc.rec_on _ _ _ aa' (λy, !is_trunc_succ_of_is_prop)),
        intro a a', apply (is_trunc_equiv_closed_rev),
        { apply tr_eq_tr_equiv},
        { exact (IH _ _ _)}}}
  end

  /- equivalences between truncated types (see also hit.trunc) -/
  definition trunc_trunc_equiv_left [constructor] (A : Type) {n m : ℕ₋₂} (H : n ≤ m)
    : trunc n (trunc m A) ≃ trunc n A :=
  begin
    note H2 := is_trunc_of_le (trunc n A) H,
    fapply equiv.MK,
    { intro x, induction x with x, induction x with x, exact tr x},
    { intro x, induction x with x, exact tr (tr x)},
    { intro x, induction x with x, reflexivity},
    { intro x, induction x with x, induction x with x, reflexivity}
  end

  definition trunc_trunc_equiv_right [constructor] (A : Type) {n m : ℕ₋₂} (H : n ≤ m)
    : trunc m (trunc n A) ≃ trunc n A :=
  begin
    apply trunc_equiv,
    exact is_trunc_of_le _ H,
  end

  definition trunc_equiv_trunc_of_le {n m : ℕ₋₂} {A B : Type} (H : n ≤ m)
    (f : trunc m A ≃ trunc m B) : trunc n A ≃ trunc n B :=
  (trunc_trunc_equiv_left A H)⁻¹ᵉ ⬝e trunc_equiv_trunc n f ⬝e trunc_trunc_equiv_left B H

  definition trunc_trunc_equiv_trunc_trunc [constructor] (n m : ℕ₋₂) (A : Type)
    : trunc n (trunc m A) ≃ trunc m (trunc n A) :=
  begin
    fapply equiv.MK: intro x; induction x with x; induction x with x,
    { exact tr (tr x)},
    { exact tr (tr x)},
    { reflexivity},
    { reflexivity}
  end

  theorem is_trunc_trunc_of_le (A : Type)
    (n : ℕ₋₂) {m k : ℕ₋₂} (H : m ≤ k) [is_trunc n (trunc k A)] : is_trunc n (trunc m A) :=
  begin
    apply is_trunc_equiv_closed,
    { apply trunc_trunc_equiv_left, exact H},
  end

  definition trunc_functor_homotopy [unfold 7] {X Y : Type} (n : ℕ₋₂) {f g : X → Y}
    (p : f ~ g) (x : trunc n X) : trunc_functor n f x = trunc_functor n g x :=
  begin
    induction x with x, esimp, exact ap tr (p x)
  end

  definition trunc_functor_homotopy_of_le {n k : ℕ₋₂} {A B : Type} (f : A → B) (H : n ≤ k) :
    to_fun (trunc_trunc_equiv_left B H) ∘
    trunc_functor n (trunc_functor k f) ∘
    to_fun (trunc_trunc_equiv_left A H)⁻¹ᵉ ~
      trunc_functor n f :=
  begin
    intro x, induction x with x, reflexivity
  end

  definition is_equiv_trunc_functor_of_le {n k : ℕ₋₂} {A B : Type} (f : A → B) (H : n ≤ k)
    [is_equiv (trunc_functor k f)] : is_equiv (trunc_functor n f) :=
  is_equiv_of_equiv_of_homotopy (trunc_equiv_trunc_of_le H (equiv.mk (trunc_functor k f) _))
                                (trunc_functor_homotopy_of_le f H)

  /- trunc_functor preserves surjectivity -/

  definition is_surjective_trunc_functor {A B : Type} (n : ℕ₋₂) (f : A → B) [H : is_surjective f]
    : is_surjective (trunc_functor n f) :=
  begin
    cases n with n: intro b,
    { exact tr (fiber.mk !center !is_prop.elim)},
    { refine @trunc.rec _ _ _ _ _ b, {intro x, exact is_trunc_of_le _ !minus_one_le_succ},
      clear b, intro b, induction H b with a p,
      exact tr (fiber.mk (tr a) (ap tr p))}
  end

  /- truncation of pointed types -/
  definition ptrunc [constructor] (n : ℕ₋₂) (X : Type*) : n-Type* :=
  ptrunctype.mk (trunc n X) _ (tr pt)

  /- pointed maps involving ptrunc -/
  definition ptrunc_functor [constructor] {X Y : Type*} (n : ℕ₋₂) (f : X →* Y)
    : ptrunc n X →* ptrunc n Y :=
  pmap.mk (trunc_functor n f) (ap tr (respect_pt f))

  definition ptr [constructor] (n : ℕ₋₂) (A : Type*) : A →* ptrunc n A :=
  pmap.mk tr idp

  definition puntrunc [constructor] (n : ℕ₋₂) (A : Type*) [is_trunc n A] : ptrunc n A →* A :=
  pmap.mk untrunc_of_is_trunc idp

  definition ptrunc.elim [constructor] (n : ℕ₋₂) {X Y : Type*} [is_trunc n Y] (f : X →* Y) :
    ptrunc n X →* Y :=
  pmap.mk (trunc.elim f) (respect_pt f)

  /- pointed equivalences involving ptrunc -/
  definition ptrunc_pequiv_ptrunc [constructor] (n : ℕ₋₂) {X Y : Type*} (H : X ≃* Y)
    : ptrunc n X ≃* ptrunc n Y :=
  pequiv_of_equiv (trunc_equiv_trunc n H) (ap tr (respect_pt H))

  definition ptrunc_pequiv [constructor] (n : ℕ₋₂) (X : Type*) [H : is_trunc n X]
    : ptrunc n X ≃* X :=
  pequiv_of_equiv (trunc_equiv n X) idp

  definition ptrunc_ptrunc_pequiv_left [constructor] (A : Type*) {n m : ℕ₋₂} (H : n ≤ m)
    : ptrunc n (ptrunc m A) ≃* ptrunc n A :=
  pequiv_of_equiv (trunc_trunc_equiv_left A H) idp

  definition ptrunc_ptrunc_pequiv_right [constructor] (A : Type*) {n m : ℕ₋₂} (H : n ≤ m)
    : ptrunc m (ptrunc n A) ≃* ptrunc n A :=
  pequiv_of_equiv (trunc_trunc_equiv_right A H) idp

  definition ptrunc_pequiv_ptrunc_of_le {n m : ℕ₋₂} {A B : Type*} (H : n ≤ m)
    (f : ptrunc m A ≃* ptrunc m B) : ptrunc n A ≃* ptrunc n B :=
  (ptrunc_ptrunc_pequiv_left A H)⁻¹ᵉ* ⬝e*
  ptrunc_pequiv_ptrunc n f ⬝e*
  ptrunc_ptrunc_pequiv_left B H

  definition ptrunc_ptrunc_pequiv_ptrunc_ptrunc [constructor] (n m : ℕ₋₂) (A : Type*)
    : ptrunc n (ptrunc m A) ≃* ptrunc m (ptrunc n A) :=
  pequiv_of_equiv (trunc_trunc_equiv_trunc_trunc n m A) idp

  definition loop_ptrunc_pequiv [constructor] (n : ℕ₋₂) (A : Type*) :
    Ω (ptrunc (n+1) A) ≃* ptrunc n (Ω A) :=
  pequiv_of_equiv !tr_eq_tr_equiv idp

  definition loop_ptrunc_pequiv_con {n : ℕ₋₂} {A : Type*} (p q : Ω (ptrunc (n+1) A)) :
    loop_ptrunc_pequiv n A (p ⬝ q) =
      tconcat (loop_ptrunc_pequiv n A p) (loop_ptrunc_pequiv n A q) :=
  encode_con p q

  definition loopn_ptrunc_pequiv (n : ℕ₋₂) (k : ℕ) (A : Type*) :
    Ω[k] (ptrunc (n+k) A) ≃* ptrunc n (Ω[k] A) :=
  begin
    revert n, induction k with k IH: intro n,
    { reflexivity},
    { refine _ ⬝e* loop_ptrunc_pequiv n (Ω[k] A),
      rewrite [loopn_succ_eq], apply loop_pequiv_loop,
      refine _ ⬝e* IH (n.+1),
      rewrite succ_add_nat}
  end

  definition loopn_ptrunc_pequiv_con {n : ℕ₋₂} {k : ℕ} {A : Type*}
    (p q : Ω[succ k] (ptrunc (n+succ k) A)) :
    loopn_ptrunc_pequiv n (succ k) A (p ⬝ q) =
    tconcat (loopn_ptrunc_pequiv n (succ k) A p)
            (loopn_ptrunc_pequiv n (succ k) A q)  :=
  begin
    refine _ ⬝ loop_ptrunc_pequiv_con _ _,
    exact ap !loop_ptrunc_pequiv !loop_pequiv_loop_con
  end

  definition loopn_ptrunc_pequiv_inv_con {n : ℕ₋₂} {k : ℕ} {A : Type*}
    (p q : ptrunc n (Ω[succ k] A)) :
    (loopn_ptrunc_pequiv n (succ k) A)⁻¹ᵉ* (tconcat p q) =
    (loopn_ptrunc_pequiv n (succ k) A)⁻¹ᵉ* p ⬝
    (loopn_ptrunc_pequiv n (succ k) A)⁻¹ᵉ* q :=
  equiv.inv_preserve_binary (loopn_ptrunc_pequiv n (succ k) A) concat tconcat
    (@loopn_ptrunc_pequiv_con n k A) p q

  /- pointed homotopies involving ptrunc -/
  definition ptrunc_functor_pcompose [constructor] {X Y Z : Type*} (n : ℕ₋₂) (g : Y →* Z)
    (f : X →* Y) : ptrunc_functor n (g ∘* f) ~* ptrunc_functor n g ∘* ptrunc_functor n f :=
  begin
    fapply phomotopy.mk,
    { apply trunc_functor_compose},
    { esimp, refine !idp_con ⬝ _, refine whisker_right _ !ap_compose'⁻¹ᵖ ⬝ _,
      esimp, refine whisker_right _ (ap_compose' tr g _) ⬝ _, exact !ap_con⁻¹},
  end

  definition ptrunc_functor_pid [constructor] (X : Type*) (n : ℕ₋₂) :
    ptrunc_functor n (pid X) ~* pid (ptrunc n X) :=
  begin
    fapply phomotopy.mk,
    { apply trunc_functor_id},
    { reflexivity},
  end

  definition ptrunc_functor_pcast [constructor] {X Y : Type*} (n : ℕ₋₂) (p : X = Y) :
    ptrunc_functor n (pcast p) ~* pcast (ap (ptrunc n) p) :=
  begin
    fapply phomotopy.mk,
    { intro x, esimp, refine !trunc_functor_cast ⬝ _, refine ap010 cast _ x,
      refine !ap_compose'⁻¹ ⬝ !ap_compose'},
    { induction p, reflexivity},
  end

  definition ptrunc_functor_phomotopy [constructor] {X Y : Type*} (n : ℕ₋₂) {f g : X →* Y}
    (p : f ~* g) : ptrunc_functor n f ~* ptrunc_functor n g :=
  begin
    fapply phomotopy.mk,
    { exact trunc_functor_homotopy n p},
    { esimp, refine !ap_con⁻¹ ⬝ _, exact ap02 tr !to_homotopy_pt},
  end

  definition pcast_ptrunc [constructor] (n : ℕ₋₂) {A B : Type*} (p : A = B) :
    pcast (ap (ptrunc n) p) ~* ptrunc_functor n (pcast p) :=
  begin
    fapply phomotopy.mk,
    { intro a, induction p, esimp, exact !trunc_functor_id⁻¹},
    { induction p, reflexivity}
  end

  definition ptrunc_elim_ptr [constructor] (n : ℕ₋₂) {X Y : Type*} [is_trunc n Y] (f : X →* Y) :
    ptrunc.elim n f ∘* ptr n X ~* f :=
  begin
    fapply phomotopy.mk,
    { reflexivity },
    { reflexivity }
  end

  definition ptrunc_elim_phomotopy (n : ℕ₋₂) {X Y : Type*} [is_trunc n Y] {f g : X →* Y}
    (H : f ~* g) : ptrunc.elim n f ~* ptrunc.elim n g :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with x, exact H x },
    { exact to_homotopy_pt H }
  end

  definition ap1_ptrunc_functor (n : ℕ₋₂) {A B : Type*} (f : A →* B) :
    Ω→ (ptrunc_functor (n.+1) f) ∘* (loop_ptrunc_pequiv n A)⁻¹ᵉ* ~*
    (loop_ptrunc_pequiv n B)⁻¹ᵉ* ∘* ptrunc_functor n (Ω→ f) :=
  begin
    fapply phomotopy.mk,
    { intro p, induction p with p,
      refine (!ap_inv⁻¹ ◾ !ap_compose⁻¹ ◾ idp) ⬝ _ ⬝ !ap_con⁻¹,
      apply whisker_right, refine _ ⬝ !ap_con⁻¹, exact whisker_left _ !ap_compose },
    { induction B with B b, induction f with f p, esimp at f, esimp at p, induction p, reflexivity }
  end

  definition ap1_ptrunc_elim (n : ℕ₋₂) {A B : Type*} (f : A →* B) [is_trunc (n.+1) B] :
    Ω→ (ptrunc.elim (n.+1) f) ∘* (loop_ptrunc_pequiv n A)⁻¹ᵉ* ~*
    ptrunc.elim n (Ω→ f) :=
  begin
    fapply phomotopy.mk,
    { intro p, induction p with p, exact idp ◾ !ap_compose⁻¹ ◾ idp },
    { reflexivity }
  end

  definition ap1_ptr (n : ℕ₋₂) (A : Type*) :
    Ω→ (ptr (n.+1) A) ~* (loop_ptrunc_pequiv n A)⁻¹ᵉ* ∘* ptr n (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, apply idp_con },
    { reflexivity }
  end

  definition ptrunc_elim_ptrunc_functor (n : ℕ₋₂) {A B C : Type*} (g : B →* C) (f : A →* B)
    [is_trunc n C] :
    ptrunc.elim n g ∘* ptrunc_functor n f ~* ptrunc.elim n (g ∘* f) :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with a, reflexivity },
    { esimp, exact !idp_con ⬝ whisker_right _ !ap_compose },
  end

end trunc open trunc

/- The truncated encode-decode method -/
namespace eq

  definition truncated_encode {k : ℕ₋₂} {A : Type} {a₀ a : A} {code : A → Type}
    [Πa, is_trunc k (code a)] (c₀ : code a₀) (p : trunc k (a₀ = a)) : code a :=
  begin
    induction p with p,
    exact transport code p c₀
  end

  definition truncated_encode_decode_method {k : ℕ₋₂} {A : Type} (a₀ a : A) (code : A → Type)
    [Πa, is_trunc k (code a)] (c₀ : code a₀)
    (decode : Π(a : A) (c : code a), trunc k (a₀ = a))
    (encode_decode : Π(a : A) (c : code a), truncated_encode c₀ (decode a c) = c)
    (decode_encode : decode a₀ c₀ = tr idp) : trunc k (a₀ = a) ≃ code a :=
  begin
    fapply equiv.MK,
    { exact truncated_encode c₀},
    { apply decode},
    { intro c, apply encode_decode},
    { intro p, induction p with p, induction p, exact decode_encode},
  end

end eq


/- some consequences for properties about functions (surjectivity etc.) -/
namespace function
  variables {A B : Type}
  definition is_surjective_of_is_equiv [instance] (f : A → B) [H : is_equiv f] : is_surjective f :=
  λb, begin esimp, apply center, apply is_trunc_trunc_of_is_trunc end

  definition is_equiv_equiv_is_embedding_times_is_surjective [constructor] (f : A → B)
    : is_equiv f ≃ (is_embedding f × is_surjective f) :=
  equiv_of_is_prop (λH, (_, _))
                    (λP, prod.rec_on P (λH₁ H₂, !is_equiv_of_is_surjective_of_is_embedding))

  /-
    Theorem 8.8.1:
    A function is an equivalence if it's an embedding and it's action on sets is an surjection
  -/
  definition is_equiv_of_is_surjective_trunc_of_is_embedding {A B : Type} (f : A → B)
    [H : is_embedding f] [H' : is_surjective (trunc_functor 0 f)] : is_equiv f :=
  have is_surjective f,
  begin
    intro b,
    induction H' (tr b) with a p,
    induction a with a, esimp at p,
    induction (tr_eq_tr_equiv _ _ _ p) with q,
    exact image.mk a q
  end,
  is_equiv_of_is_surjective_of_is_embedding f

  /-
    Corollary 8.8.2:
    A function f is an equivalence if Ωf and trunc_functor 0 f are equivalences
  -/
  definition is_equiv_of_is_equiv_ap1_of_is_equiv_trunc {A B : Type} (f : A → B)
    [H : Πa, is_equiv (ap1 (pmap_of_map f a))] [H' : is_equiv (trunc_functor 0 f)] :
    is_equiv f :=
  have is_embedding f,
  begin
    intro a a',
    apply is_equiv_of_imp_is_equiv,
    intro p,
    note q := ap (@tr 0 _) p,
    note r := @(eq_of_fn_eq_fn' (trunc_functor 0 f)) _ (tr a) (tr a') q,
    induction (tr_eq_tr_equiv _ _ _ r) with s,
    induction s,
    apply is_equiv.homotopy_closed (ap1 (pmap_of_map f a)),
    intro p, apply idp_con
  end,
  is_equiv_of_is_surjective_trunc_of_is_embedding f

  -- Whitehead's principle itself is in homotopy.homotopy_group, since it needs the definition of
  -- a homotopy group.

end function
