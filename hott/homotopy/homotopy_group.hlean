/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Clive Newstead

-/

import algebra.homotopy_group .connectedness

open eq is_trunc trunc_index pointed algebra trunc nat homotopy fiber pointed

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
  open sphere.ops sphere_index
  theorem homotopy_group_sphere_le (n k : ℕ) (H : k < n) : is_contr (π[k] (S. n)) :=
  begin
    cases n with n,
    { exfalso, apply not_lt_zero, exact H},
    { have H2 : k ≤ n, from le_of_lt_succ H,
      apply @(trivial_homotopy_group_of_is_conn _ H2)}
  end
  end

  theorem is_contr_HG_fiber_of_is_connected {A B : Type*} (k n : ℕ) (f : A →* B)
    [H : is_conn_fun n f] (H2 : k ≤ n) : is_contr (π[k] (pfiber f)) :=
  @(trivial_homotopy_group_of_is_conn (pfiber f) H2) (H pt)


end is_trunc
