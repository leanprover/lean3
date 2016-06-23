/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

homotopy groups of a pointed space
-/

import .trunc_group types.trunc .group_theory

open nat eq pointed trunc is_trunc algebra group function equiv unit is_equiv

-- TODO: consistently make n an argument before A
namespace eq

  definition phomotopy_group [reducible] [constructor] (n : ℕ) (A : Type*) : Set* :=
  ptrunc 0 (Ω[n] A)

  definition homotopy_group [reducible] (n : ℕ) (A : Type*) : Type :=
  phomotopy_group n A

  notation `π*[`:95 n:0 `] `:0 := phomotopy_group n
  notation `π[`:95  n:0 `] `:0 :=  homotopy_group n

  definition group_homotopy_group [instance] [constructor] [reducible] (n : ℕ) (A : Type*)
    : group (π[succ n] A) :=
  trunc_group concat inverse idp con.assoc idp_con con_idp con.left_inv

  definition group_homotopy_group2 [instance] (k : ℕ) (A : Type*) :
    group (carrier (ptrunctype.to_pType (π*[k + 1] A))) :=
  group_homotopy_group k A

  definition comm_group_homotopy_group [constructor] [reducible] (n : ℕ) (A : Type*)
    : comm_group (π[succ (succ n)] A) :=
  trunc_comm_group concat inverse idp con.assoc idp_con con_idp con.left_inv eckmann_hilton

  local attribute comm_group_homotopy_group [instance]

  definition ghomotopy_group [constructor] (n : ℕ) (A : Type*) : Group :=
  Group.mk (π[succ n] A) _

  definition cghomotopy_group [constructor] (n : ℕ) (A : Type*) : CommGroup :=
  CommGroup.mk (π[succ (succ n)] A) _

  definition fundamental_group [constructor] (A : Type*) : Group :=
  ghomotopy_group zero A

  notation `πg[`:95  n:0 ` +1] `:0 A:95 := ghomotopy_group n A
  notation `πag[`:95 n:0 ` +2] `:0 A:95 := cghomotopy_group n A

  notation `π₁` := fundamental_group -- should this be notation for the group or pointed type?

  definition tr_mul_tr {n : ℕ} {A : Type*} (p q : Ω[n + 1] A) :
    tr p *[πg[n+1] A] tr q = tr (p ⬝ q) :=
  by reflexivity

  definition tr_mul_tr' {n : ℕ} {A : Type*} (p q : Ω[succ n] A)
    : tr p *[π[succ n] A] tr q = tr (p ⬝ q) :=
  idp

  definition phomotopy_group_pequiv [constructor] (n : ℕ) {A B : Type*} (H : A ≃* B)
    : π*[n] A ≃* π*[n] B :=
  ptrunc_pequiv_ptrunc 0 (loopn_pequiv_loopn n H)

  definition phomotopy_group_pequiv_loop_ptrunc [constructor] (k : ℕ) (A : Type*) :
    π*[k] A ≃* Ω[k] (ptrunc k A) :=
  begin
    refine !iterated_loop_ptrunc_pequiv⁻¹ᵉ* ⬝e* _,
    exact loopn_pequiv_loopn k (pequiv_of_eq begin rewrite [trunc_index.zero_add] end)
  end

  open trunc_index
  definition phomotopy_group_ptrunc_of_le [constructor] {k n : ℕ} (H : k ≤ n) (A : Type*) :
    π*[k] (ptrunc n A) ≃* π*[k] A :=
  calc
    π*[k] (ptrunc n A) ≃* Ω[k] (ptrunc k (ptrunc n A))
             : phomotopy_group_pequiv_loop_ptrunc k (ptrunc n A)
      ... ≃* Ω[k] (ptrunc k A)
             : loopn_pequiv_loopn k (ptrunc_ptrunc_pequiv_left A (of_nat_le_of_nat H))
      ... ≃* π*[k] A : (phomotopy_group_pequiv_loop_ptrunc k A)⁻¹ᵉ*

  definition phomotopy_group_ptrunc [constructor] (k : ℕ) (A : Type*) :
    π*[k] (ptrunc k A) ≃* π*[k] A :=
  phomotopy_group_ptrunc_of_le (le.refl k) A

  theorem trivial_homotopy_of_is_set (A : Type*) [H : is_set A] (n : ℕ) : πg[n+1] A ≃g G0 :=
  begin
    apply trivial_group_of_is_contr,
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc,
    apply is_trunc_succ_succ_of_is_set
  end

  definition phomotopy_group_succ_out (A : Type*) (n : ℕ) : π*[n + 1] A = π₁ Ω[n] A := idp

  definition phomotopy_group_succ_in (A : Type*) (n : ℕ) : π*[n + 1] A = π*[n] (Ω A) :> Type* :=
  ap (ptrunc 0) (loop_space_succ_eq_in A n)

  definition ghomotopy_group_succ_out (A : Type*) (n : ℕ) : πg[n +1] A = π₁ Ω[n] A := idp

  definition phomotopy_group_succ_in_con {A : Type*} {n : ℕ} (g h : πg[succ n +1] A) :
    pcast (phomotopy_group_succ_in A (succ n)) (g * h) =
    pcast (phomotopy_group_succ_in A (succ n)) g *
    pcast (phomotopy_group_succ_in A (succ n)) h :=
  begin
    induction g with p, induction h with q, esimp,
    rewrite [-+ tr_eq_cast_ap, ↑phomotopy_group_succ_in, -+ tr_compose],
    refine ap (transport _ _) !tr_mul_tr' ⬝ _,
    rewrite [+ trunc_transport],
    apply ap tr, apply loop_space_succ_eq_in_concat,
  end

  definition ghomotopy_group_succ_in (A : Type*) (n : ℕ) : πg[succ n +1] A ≃g πg[n +1] Ω A :=
  begin
    fapply isomorphism_of_equiv,
    { apply equiv_of_eq, exact ap (ptrunc 0) (loop_space_succ_eq_in A (succ n))},
    { exact abstract [irreducible] begin refine trunc.rec _, intro p, refine trunc.rec _, intro q,
      rewrite [▸*,-+tr_eq_cast_ap, +trunc_transport], refine !trunc_transport ⬝ _, apply ap tr,
      apply loop_space_succ_eq_in_concat end end},
  end

  definition phomotopy_group_functor [constructor] (n : ℕ) {A B : Type*} (f : A →* B)
    : π*[n] A →* π*[n] B :=
  ptrunc_functor 0 (apn n f)

  definition homotopy_group_functor (n : ℕ) {A B : Type*} (f : A →* B) : π[n] A → π[n] B :=
  phomotopy_group_functor n f

  notation `π→*[`:95 n:0 `] `:0 := phomotopy_group_functor n
  notation `π→[`:95  n:0 `] `:0 :=  homotopy_group_functor n

  definition phomotopy_group_functor_phomotopy [constructor] (n : ℕ) {A B : Type*} {f g : A →* B}
    (p : f ~* g) : π→*[n] f ~* π→*[n] g :=
  ptrunc_functor_phomotopy 0 (apn_phomotopy n p)

  definition phomotopy_group_functor_compose [constructor] (n : ℕ) {A B C : Type*} (g : B →* C)
    (f : A →* B) : π→*[n] (g ∘* f) ~* π→*[n] g ∘* π→*[n] f :=
  ptrunc_functor_phomotopy 0 !apn_compose ⬝* !ptrunc_functor_pcompose

  definition is_equiv_homotopy_group_functor [constructor] (n : ℕ) {A B : Type*} (f : A →* B)
    [is_equiv f] : is_equiv (π→[n] f) :=
  @(is_equiv_trunc_functor 0 _) !is_equiv_apn

  definition phomotopy_group_functor_succ_phomotopy_in (n : ℕ) {A B : Type*} (f : A →* B) :
    pcast (phomotopy_group_succ_in B n) ∘* π→*[n + 1] f ~*
    π→*[n] (Ω→ f) ∘* pcast (phomotopy_group_succ_in A n) :=
  begin
    refine pwhisker_right _ (pcast_ptrunc 0 (loop_space_succ_eq_in B n)) ⬝* _,
    refine _ ⬝* pwhisker_left _ (pcast_ptrunc 0 (loop_space_succ_eq_in A n))⁻¹*,
    refine !ptrunc_functor_pcompose⁻¹* ⬝* _ ⬝* !ptrunc_functor_pcompose,
    exact ptrunc_functor_phomotopy 0 (apn_succ_phomotopy_in n f)
  end

  definition is_equiv_phomotopy_group_functor_ap1 (n : ℕ) {A B : Type*} (f : A →* B)
    [is_equiv (π→*[n + 1] f)] : is_equiv (π→*[n] (Ω→ f)) :=
  have is_equiv (pcast (phomotopy_group_succ_in B n) ∘* π→*[n + 1] f),
  from is_equiv_compose _ (π→*[n + 1] f),
  have is_equiv (π→*[n] (Ω→ f) ∘ pcast (phomotopy_group_succ_in A n)),
  from is_equiv.homotopy_closed _ (phomotopy_group_functor_succ_phomotopy_in n f),
  is_equiv.cancel_right (pcast (phomotopy_group_succ_in A n)) _

  definition tinverse [constructor] {X : Type*} : π*[1] X →* π*[1] X :=
  ptrunc_functor 0 pinverse

  definition is_equiv_tinverse [constructor] (A : Type*) : is_equiv (@tinverse A) :=
  by apply @is_equiv_trunc_functor; apply is_equiv_eq_inverse

  definition ptrunc_functor_pinverse [constructor] {X : Type*}
    : ptrunc_functor 0 (@pinverse X) ~* @tinverse X :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { reflexivity}
  end

  definition phomotopy_group_functor_mul [constructor] (n : ℕ) {A B : Type*} (g : A →* B)
    (p q : πg[n+1] A) :
    (π→[n + 1] g) (p *[πg[n+1] A] q) = (π→[n + 1] g) p *[πg[n+1] B] (π→[n + 1] g) q :=
  begin
    unfold [ghomotopy_group, homotopy_group] at *,
    refine @trunc.rec _ _ _ (λq, !is_trunc_eq) _ p, clear p, intro p,
    refine @trunc.rec _ _ _ (λq, !is_trunc_eq) _ q, clear q, intro q,
    apply ap tr, apply apn_con
  end

  definition homotopy_group_homomorphism [constructor] (n : ℕ) {A B : Type*} (f : A →* B)
    : πg[n+1] A →g πg[n+1] B :=
  begin
    fconstructor,
    { exact phomotopy_group_functor (n+1) f},
    { apply phomotopy_group_functor_mul}
  end

  definition homotopy_group_isomorphism_of_pequiv [constructor] (n : ℕ) {A B : Type*} (f : A ≃* B)
    : πg[n+1] A ≃g πg[n+1] B :=
  begin
    apply isomorphism.mk (homotopy_group_homomorphism n f),
    esimp, apply is_equiv_trunc_functor, apply is_equiv_apn,
  end

  definition homotopy_group_add (A : Type*) (n m : ℕ) : πg[n+m +1] A ≃g πg[n +1] Ω[m] A :=
  begin
    revert A, induction m with m IH: intro A,
    { reflexivity},
    { esimp [iterated_ploop_space, nat.add], refine !ghomotopy_group_succ_in ⬝g _, refine !IH ⬝g _,
      apply homotopy_group_isomorphism_of_pequiv,
      exact pequiv_of_eq !loop_space_succ_eq_in⁻¹}
  end

  theorem trivial_homotopy_add_of_is_set_loop_space {A : Type*} {n : ℕ} (m : ℕ)
    (H : is_set (Ω[n] A)) : πg[m+n+1] A ≃g G0 :=
  !homotopy_group_add ⬝g !trivial_homotopy_of_is_set

  theorem trivial_homotopy_le_of_is_set_loop_space {A : Type*} {n : ℕ} (m : ℕ) (H1 : n ≤ m)
    (H2 : is_set (Ω[n] A)) : πg[m+1] A ≃g G0 :=
  obtain (k : ℕ) (p : n + k = m), from le.elim H1,
  isomorphism_of_eq (ap (λx, πg[x+1] A) (p⁻¹ ⬝ add.comm n k)) ⬝g
  trivial_homotopy_add_of_is_set_loop_space k H2

  definition phomotopy_group_pequiv_loop_ptrunc_con {k : ℕ} {A : Type*} (p q : πg[k +1] A) :
    phomotopy_group_pequiv_loop_ptrunc (succ k) A (p * q) =
    phomotopy_group_pequiv_loop_ptrunc (succ k) A p ⬝
    phomotopy_group_pequiv_loop_ptrunc (succ k) A q :=
  begin
    refine _ ⬝ !loopn_pequiv_loopn_con,
    exact ap (loopn_pequiv_loopn _ _) !iterated_loop_ptrunc_pequiv_inv_con
  end

  definition phomotopy_group_pequiv_loop_ptrunc_inv_con {k : ℕ} {A : Type*}
    (p q : Ω[succ k] (ptrunc (succ k) A)) :
    (phomotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* (p ⬝ q) =
    (phomotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* p *
    (phomotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* q :=
  inv_preserve_binary (phomotopy_group_pequiv_loop_ptrunc (succ k) A) mul concat
    (@phomotopy_group_pequiv_loop_ptrunc_con k A) p q

  definition ghomotopy_group_ptrunc [constructor] (k : ℕ) (A : Type*) :
    πg[k+1] (ptrunc (k+1) A) ≃g πg[k+1] A :=
  begin
    fapply isomorphism_of_equiv,
    { exact phomotopy_group_ptrunc (k+1) A},
    { intro g₁ g₂, esimp,
      refine _ ⬝ !phomotopy_group_pequiv_loop_ptrunc_inv_con,
      apply ap ((phomotopy_group_pequiv_loop_ptrunc (k+1) A)⁻¹ᵉ*),
      refine _ ⬝ !loopn_pequiv_loopn_con ,
      apply ap (loopn_pequiv_loopn (k+1) _),
      apply phomotopy_group_pequiv_loop_ptrunc_con}
  end

  /- some homomorphisms -/

  definition is_homomorphism_cast_loop_space_succ_eq_in {A : Type*} (n : ℕ) :
    is_homomorphism
      (cast (ap (trunc 0 ∘ pointed.carrier) (loop_space_succ_eq_in A (succ n)))
        : πg[n+1+1] A → πg[n+1] Ω A) :=
  begin
    intro g h, induction g with g, induction h with h,
    xrewrite [tr_mul_tr, - + fn_cast_eq_cast_fn _ (λn, tr), tr_mul_tr, ↑cast, -tr_compose,
              loop_space_succ_eq_in_concat, - + tr_compose],
  end

  definition is_homomorphism_inverse (A : Type*) (n : ℕ)
    : is_homomorphism (λp, p⁻¹ : πag[n+2] A → πag[n+2] A) :=
  begin
    intro g h, rewrite mul.comm,
    induction g with g, induction h with h,
    exact ap tr !con_inv
  end

  notation `π→g[`:95  n:0 ` +1] `:0 f:95 := homotopy_group_homomorphism n f

end eq
