/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Clive Newstead

-/

import .LES_of_homotopy_groups .sphere .complex_hopf

open eq is_trunc trunc_index pointed algebra trunc nat is_conn fiber pointed

namespace is_trunc
  -- Lemma 8.3.1
  theorem trivial_homotopy_group_of_is_trunc (A : Type*) (n k : ℕ) [is_trunc n A] (H : n ≤ k)
    : is_contr (πg[k+1] A) :=
  begin
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc,
    apply @is_trunc_of_le A n _,
    rewrite [succ_sub_two_succ k],
    exact of_nat_le_of_nat H,
  end

  -- Lemma 8.3.2
  theorem trivial_homotopy_group_of_is_conn (A : Type*) {k n : ℕ} (H : k ≤ n) [is_conn n A]
    : is_contr (π[k] A) :=
  begin
      have H3 : is_contr (ptrunc k A), from is_conn_of_le A (of_nat_le_of_nat H),
      have H4 : is_contr (Ω[k](ptrunc k A)), from !is_trunc_loop_of_is_trunc,
      apply is_trunc_equiv_closed_rev,
      { apply equiv_of_pequiv (phomotopy_group_pequiv_loop_ptrunc k A)}
  end

  -- Corollary 8.3.3
  section
  open sphere sphere.ops sphere_index
  theorem homotopy_group_sphere_le (n k : ℕ) (H : k < n) : is_contr (π[k] (S. n)) :=
  begin
    cases n with n,
    { exfalso, apply not_lt_zero, exact H},
    { have H2 : k ≤ n, from le_of_lt_succ H,
      apply @(trivial_homotopy_group_of_is_conn _ H2) }
  end
  end

  theorem is_contr_HG_fiber_of_is_connected {A B : Type*} (k n : ℕ) (f : A →* B)
    [H : is_conn_fun n f] (H2 : k ≤ n) : is_contr (π[k] (pfiber f)) :=
  @(trivial_homotopy_group_of_is_conn (pfiber f) H2) (H pt)

  /- Corollaries of the LES of homotopy groups -/
  local attribute comm_group.to_group [coercion]
  local attribute is_equiv_tinverse [instance]
  open prod chain_complex group fin equiv function is_equiv lift

  /-
    Because of the construction of the LES this proof only gives us this result when
    A and B live in the same universe (because Lean doesn't have universe cumulativity).
    However, below we also proof that it holds for A and B in arbitrary universes.
  -/
  theorem is_equiv_π_of_is_connected'.{u} {A B : pType.{u}} {n k : ℕ} (f : A →* B)
     (H2 : k ≤ n) [H : is_conn_fun n f] : is_equiv (π→[k] f) :=
  begin
    cases k with k,
    { /- k = 0 -/
      change (is_equiv (trunc_functor 0 f)), apply is_equiv_trunc_functor_of_is_conn_fun,
      refine is_conn_fun_of_le f (zero_le_of_nat n)},
    { /- k > 0 -/
     have H2' : k ≤ n, from le.trans !self_le_succ H2,
      exact
      @is_equiv_of_trivial _
        (LES_of_homotopy_groups f) _
        (is_exact_LES_of_homotopy_groups f (k, 2))
        (is_exact_LES_of_homotopy_groups f (succ k, 0))
        (@is_contr_HG_fiber_of_is_connected A B k n f H H2')
        (@is_contr_HG_fiber_of_is_connected A B (succ k) n f H H2)
        (@pgroup_of_group _ (group_LES_of_homotopy_groups f k 0) idp)
        (@pgroup_of_group _ (group_LES_of_homotopy_groups f k 1) idp)
        (homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun f (k, 0)))},
  end

  theorem is_equiv_π_of_is_connected.{u v} {A : pType.{u}} {B : pType.{v}} {n k : ℕ} (f : A →* B)
    (H2 : k ≤ n) [H : is_conn_fun n f] : is_equiv (π→[k] f) :=
  begin
    have π→*[k] pdown.{v u} ∘* π→*[k] (plift_functor f) ∘* π→*[k] pup.{u v} ~* π→*[k] f,
    begin
      refine pwhisker_left _ !phomotopy_group_functor_compose⁻¹* ⬝* _,
      refine !phomotopy_group_functor_compose⁻¹* ⬝* _,
      apply phomotopy_group_functor_phomotopy, apply plift_functor_phomotopy
    end,
    have π→[k] pdown.{v u} ∘ π→[k] (plift_functor f) ∘ π→[k] pup.{u v} ~ π→[k] f, from this,
    apply is_equiv.homotopy_closed, rotate 1,
    { exact this},
    { do 2 apply is_equiv_compose,
      { apply is_equiv_homotopy_group_functor, apply to_is_equiv !equiv_lift},
      { refine @(is_equiv_π_of_is_connected' _ H2) _, apply is_conn_fun_lift_functor},
      { apply is_equiv_homotopy_group_functor, apply to_is_equiv !equiv_lift⁻¹ᵉ}}
  end

  definition π_equiv_π_of_is_connected {A B : Type*} {n k : ℕ} (f : A →* B)
     (H2 : k ≤ n) [H : is_conn_fun n f] : π*[k] A ≃* π*[k] B :=
  pequiv_of_pmap (π→*[k] f) (is_equiv_π_of_is_connected f H2)

  -- TODO: prove this for A and B in different universe levels
  theorem is_surjective_π_of_is_connected.{u} {A B : pType.{u}} (n : ℕ) (f : A →* B)
    [H : is_conn_fun n f] : is_surjective (π→[n + 1] f) :=
  @is_surjective_of_trivial _
    (LES_of_homotopy_groups f) _
    (is_exact_LES_of_homotopy_groups f (n, 2))
    (@is_contr_HG_fiber_of_is_connected A B n n f H !le.refl)

  /-
    Theorem 8.8.3: Whitehead's principle
  -/
  definition whiteheads_principle (n : ℕ₋₂) {A B : Type}
    [HA : is_trunc n A] [HB : is_trunc n B] (f : A → B) (H' : is_equiv (trunc_functor 0 f))
    (H : Πa k, is_equiv (π→*[k + 1] (pmap_of_map f a))) : is_equiv f :=
  begin
    revert A B HA HB f H' H, induction n with n IH: intros,
    { apply is_equiv_of_is_contr},
    have Πa, is_equiv (Ω→ (pmap_of_map f a)),
    begin
      intro a,
      apply IH, do 2 (esimp; exact _),
      { rexact H a 0},
      intro p k,
      have is_equiv (π→*[k + 1] (Ω→(pmap_of_map f a))),
        from is_equiv_phomotopy_group_functor_ap1 (k+1) (pmap_of_map f a),
      have Π(b : A) (p : a = b),
        is_equiv (pmap.to_fun (π→*[k + 1] (pmap_of_map (ap f) p))),
      begin
        intro b p, induction p, apply is_equiv.homotopy_closed, exact this,
        refine phomotopy_group_functor_phomotopy _ _,
        apply ap1_pmap_of_map
      end,
      have is_equiv (phomotopy_group_pequiv _
                      (pequiv_of_eq_pt (!idp_con⁻¹ : ap f p = Ω→ (pmap_of_map f a) p)) ∘
           pmap.to_fun (π→*[k + 1] (pmap_of_map (ap f) p))),
      begin
        apply is_equiv_compose, exact this a p,
      end,
      apply is_equiv.homotopy_closed, exact this,
      refine !phomotopy_group_functor_compose⁻¹* ⬝* _,
      apply phomotopy_group_functor_phomotopy,
      fapply phomotopy.mk,
      { esimp, intro q, refine !idp_con⁻¹},
      { esimp, refine !idp_con⁻¹},
    end,
    apply is_equiv_of_is_equiv_ap1_of_is_equiv_trunc
  end

end is_trunc
