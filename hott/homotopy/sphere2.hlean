/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Calculating homotopy groups of spheres.

In this file we calculate
π₂(S²) = Z
πₙ(S²) = πₙ(S³) for n > 2
πₙ(Sⁿ) = Z for n > 0
π₂(S³) = Z
-/

import .homotopy_group .freudenthal
open eq group algebra is_equiv equiv fin prod chain_complex pointed fiber nat is_trunc trunc_index
     sphere.ops trunc is_conn susp

namespace sphere
  /- Corollaries of the complex hopf fibration combined with the LES of homotopy groups -/
  open sphere sphere.ops int circle hopf

  definition π2S2 : πg[1+1] (S* 2) ≃g gℤ :=
  begin
    refine _ ⬝g fundamental_group_of_circle,
    refine _ ⬝g homotopy_group_isomorphism_of_pequiv _ pfiber_complex_phopf,
    fapply isomorphism_of_equiv,
    { fapply equiv.mk,
      { exact cc_to_fn (LES_of_homotopy_groups complex_phopf) (1, 2)},
      { refine @is_equiv_of_trivial _
        _ _
        (is_exact_LES_of_homotopy_groups _ (1, 1))
        (is_exact_LES_of_homotopy_groups _ (1, 2))
        _
        _
        (@pgroup_of_group _ (group_LES_of_homotopy_groups complex_phopf _ _) idp)
        (@pgroup_of_group _ (group_LES_of_homotopy_groups complex_phopf _ _) idp)
        _,
        { rewrite [LES_of_homotopy_groups_1, ▸*],
          have H : 1 ≤[ℕ] 2, from !one_le_succ,
          apply trivial_homotopy_group_of_is_conn, exact H, rexact is_conn_psphere 3},
        { refine tr_rev (λx, is_contr (ptrunctype._trans_of_to_pType x))
                        (LES_of_homotopy_groups_1 complex_phopf 2) _,
          apply trivial_homotopy_group_of_is_conn, apply le.refl, rexact is_conn_psphere 3},
        { exact homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun _ (0, 2))}}},
    { exact homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun _ (0, 2))}
  end

  open circle
  definition πnS3_eq_πnS2 (n : ℕ) : πg[n+2 +1] (S* 3) ≃g πg[n+2 +1] (S* 2) :=
  begin
    fapply isomorphism_of_equiv,
    { fapply equiv.mk,
      { exact cc_to_fn (LES_of_homotopy_groups complex_phopf) (n+3, 0)},
      { have H : is_trunc 1 (pfiber complex_phopf),
        from @(is_trunc_equiv_closed_rev _ pfiber_complex_phopf) is_trunc_circle,
        refine @is_equiv_of_trivial _
        _ _
        (is_exact_LES_of_homotopy_groups _ (n+2, 2))
        (is_exact_LES_of_homotopy_groups _ (n+3, 0))
        _
        _
        (@pgroup_of_group _ (group_LES_of_homotopy_groups complex_phopf _ _) idp)
        (@pgroup_of_group _ (group_LES_of_homotopy_groups complex_phopf _ _) idp)
        _,
        { rewrite [▸*, LES_of_homotopy_groups_2 _ (n +[ℕ] 2)],
          have H2 : 1 ≤[ℕ] n + 1, from !one_le_succ,
          exact @trivial_ghomotopy_group_of_is_trunc _ _ _ H H2},
        { refine tr_rev (λx, is_contr (ptrunctype._trans_of_to_pType x))
                        (LES_of_homotopy_groups_2 complex_phopf _) _,
          have H2 : 1 ≤[ℕ] n + 2, from !one_le_succ,
          apply trivial_ghomotopy_group_of_is_trunc _ _ _ H2},
        { exact homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun _ (n+2, 0))}}},
    { exact homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun _ (n+2, 0))}
  end

  definition sphere_stability_pequiv (k n : ℕ) (H : k + 2 ≤ 2 * n) :
    π[k + 1] (S* (n+1)) ≃* π[k] (S* n) :=
  begin rewrite [+ psphere_eq_iterate_susp], exact iterate_susp_stability_pequiv empty H end

  definition stability_isomorphism (k n : ℕ) (H : k + 3 ≤ 2 * n)
    : πg[k+1 +1] (S* (n+1)) ≃g πg[k+1] (S* n) :=
  begin rewrite [+ psphere_eq_iterate_susp], exact iterate_susp_stability_isomorphism empty H end

  open int circle hopf
  definition πnSn (n : ℕ) : πg[n+1] (S* (succ n)) ≃g gℤ :=
  begin
    cases n with n IH,
    { exact fundamental_group_of_circle},
    { induction n with n IH,
      { exact π2S2},
      { refine _ ⬝g IH, apply stability_isomorphism,
        rexact add_mul_le_mul_add n 1 2}}
  end

  theorem not_is_trunc_sphere (n : ℕ) : ¬is_trunc n (S* (succ n)) :=
  begin
    intro H,
    note H2 := trivial_ghomotopy_group_of_is_trunc (S* (succ n)) n n !le.refl,
    have H3 : is_contr ℤ, from is_trunc_equiv_closed _ (equiv_of_isomorphism (πnSn n)),
    have H4 : (0 : ℤ) ≠ (1 : ℤ), from dec_star,
    apply H4,
    apply is_prop.elim,
  end

  section
    open sphere_index

    definition not_is_trunc_sphere' (n : ℕ₋₁) : ¬is_trunc n (S (n.+1)) :=
    begin
      cases n with n,
      { esimp [sphere.ops.S, sphere], intro H,
        have H2 : is_prop bool, from @(is_trunc_equiv_closed -1 sphere_equiv_bool) H,
        have H3 : bool.tt ≠ bool.ff, from dec_star, apply H3, apply is_prop.elim},
      { intro H, apply not_is_trunc_sphere (add_one n),
        rewrite [▸*, trunc_index_of_nat_add_one, -add_one_succ,
                 sphere_index_of_nat_add_one],
        exact H}
    end

  end

  definition π3S2 : πg[2+1] (S* 2) ≃g gℤ :=
  (πnS3_eq_πnS2 0)⁻¹ᵍ ⬝g πnSn 2

end sphere
