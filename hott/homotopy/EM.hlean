/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Eilenberg MacLane spaces
-/

import hit.groupoid_quotient homotopy.hopf homotopy.freudenthal homotopy.homotopy_group
open algebra pointed nat eq category group is_trunc iso unit trunc equiv is_conn function is_equiv
     trunc_index

namespace EM
  open groupoid_quotient

  variables {G : Group}
  definition EM1' (G : Group) : Type :=
  groupoid_quotient (Groupoid_of_Group G)
  definition EM1 [constructor] (G : Group) : Type* :=
  pointed.MK (EM1' G) (elt star)

  definition base : EM1' G := elt star
  definition pth : G → base = base := pth
  definition resp_mul (g h : G) : pth (g * h) = pth g ⬝ pth h := resp_comp h g
  definition resp_one : pth (1 : G) = idp :=
  resp_id star

  definition resp_inv (g : G) : pth (g⁻¹) = (pth g)⁻¹ :=
  resp_inv g

  local attribute pointed.MK pointed.carrier EM1 EM1' [reducible]
  protected definition rec {P : EM1' G → Type} [H : Π(x : EM1' G), is_trunc 1 (P x)]
    (Pb : P base) (Pp : Π(g : G), Pb =[pth g] Pb)
    (Pmul : Π(g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g ⬝o Pp h) (x : EM1' G) :
    P x :=
  begin
    induction x,
    { induction g, exact Pb},
    { induction a, induction b, exact Pp f},
    { induction a, induction b, induction c, exact Pmul f g}
  end

  protected definition rec_on {P : EM1' G → Type} [H : Π(x : EM1' G), is_trunc 1 (P x)]
    (x : EM1' G) (Pb : P base) (Pp : Π(g : G), Pb =[pth g] Pb)
    (Pmul : Π(g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g ⬝o Pp h) : P x :=
  EM.rec Pb Pp Pmul x

  protected definition set_rec {P : EM1' G → Type} [H : Π(x : EM1' G), is_set (P x)]
    (Pb : P base) (Pp : Π(g : G), Pb =[pth g] Pb) (x : EM1' G) : P x :=
  EM.rec Pb Pp !center x

  protected definition prop_rec {P : EM1' G → Type} [H : Π(x : EM1' G), is_prop (P x)]
    (Pb : P base) (x : EM1' G) : P x :=
  EM.rec Pb !center !center x

  definition rec_pth {P : EM1' G → Type} [H : Π(x : EM1' G), is_trunc 1 (P x)]
    {Pb : P base} {Pp : Π(g : G), Pb =[pth g] Pb}
    (Pmul : Π(g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g ⬝o Pp h)
    (g : G) : apd (EM.rec Pb Pp Pmul) (pth g) = Pp g :=
  proof !rec_pth qed

  protected definition elim {P : Type} [is_trunc 1 P] (Pb : P) (Pp : Π(g : G), Pb = Pb)
    (Pmul : Π(g h : G), Pp (g * h) = Pp g ⬝ Pp h) (x : EM1' G) : P :=
  begin
    induction x,
    { exact Pb},
    { exact Pp f},
    { exact Pmul f g}
  end

  protected definition elim_on [reducible] {P : Type} [is_trunc 1 P] (x : EM1' G)
    (Pb : P) (Pp : G → Pb = Pb) (Pmul : Π(g h : G), Pp (g * h) = Pp g ⬝ Pp h) : P :=
  EM.elim Pb Pp Pmul x

  protected definition set_elim [reducible] {P : Type} [is_set P] (Pb : P) (Pp : G → Pb = Pb)
    (x : EM1' G) : P :=
  EM.elim Pb Pp !center x

  protected definition prop_elim [reducible] {P : Type} [is_prop P] (Pb : P) (x : EM1' G) : P :=
  EM.elim Pb !center !center x

  definition elim_pth {P : Type} [is_trunc 1 P] {Pb : P} {Pp : G → Pb = Pb}
    (Pmul : Π(g h : G), Pp (g * h) = Pp g ⬝ Pp h) (g : G) : ap (EM.elim Pb Pp Pmul) (pth g) = Pp g :=
  proof !elim_pth qed

  protected definition elim_set.{u} (Pb : Set.{u}) (Pp : Π(g : G), Pb ≃ Pb)
    (Pmul : Π(g h : G) (x : Pb), Pp (g * h) x = Pp h (Pp g x)) (x : EM1' G) : Set.{u} :=
  groupoid_quotient.elim_set (λu, Pb) (λu v, Pp) (λu v w g h, proof Pmul h g qed) x

  theorem elim_set_pth {Pb : Set} {Pp : Π(g : G), Pb ≃ Pb}
    (Pmul : Π(g h : G) (x : Pb), Pp (g * h) x = Pp h (Pp g x)) (g : G) :
    transport (EM.elim_set Pb Pp Pmul) (pth g) = Pp g :=
  !elim_set_pth

end EM

attribute EM.base [constructor]
attribute EM.rec EM.elim [unfold 7] [recursor 7]
attribute EM.rec_on EM.elim_on [unfold 4]
attribute EM.set_rec EM.set_elim [unfold 6]
attribute EM.prop_rec EM.prop_elim EM.elim_set [unfold 5]

namespace EM
  open groupoid_quotient

  variables (G : Group)
  definition base_eq_base_equiv : (base = base :> EM1 G) ≃ G :=
  !elt_eq_elt_equiv

  definition fundamental_group_EM1 : π₁ (EM1 G) ≃g G :=
  begin
    fapply isomorphism_of_equiv,
    { exact trunc_equiv_trunc 0 !base_eq_base_equiv ⬝e trunc_equiv 0 G},
    { intros g h, induction g with p, induction h with q,
      exact encode_con p q}
  end

  proposition is_trunc_EM1 [instance] : is_trunc 1 (EM1 G) :=
  !is_trunc_groupoid_quotient

  proposition is_trunc_EM1' [instance] : is_trunc 1 (EM1' G) :=
  !is_trunc_groupoid_quotient

  proposition is_conn_EM1' [instance] : is_conn 0 (EM1' G) :=
  by apply @is_conn_groupoid_quotient; esimp; exact _

  proposition is_conn_EM1 [instance] : is_conn 0 (EM1 G) :=
  is_conn_EM1' G

  variable {G}
  definition EM1_map [unfold 7] {X : Type*} (e : G → Ω X)
    (r : Πg h, e (g * h) = e g ⬝ e h) [is_conn 0 X] [is_trunc 1 X] : EM1 G → X :=
  begin
    intro x, induction x using EM.elim,
    { exact Point X },
    { exact e g },
    { exact r g h }
  end

  /- Uniqueness of K(G, 1) -/

  definition EM1_pmap [constructor] {X : Type*} (e : G → Ω X)
    (r : Πg h, e (g * h) = e g ⬝ e h) [is_conn 0 X] [is_trunc 1 X] : EM1 G →* X :=
  pmap.mk (EM1_map e r) idp

  variable (G)
  definition loop_EM1 [constructor] : G ≃* Ω (EM1 G) :=
  (pequiv_of_equiv (base_eq_base_equiv G) idp)⁻¹ᵉ*

  variable {G}
  definition loop_EM1_pmap {X : Type*} (e : G →* Ω X)
    (r : Πg h, e (g * h) = e g ⬝ e h) [is_conn 0 X] [is_trunc 1 X] :
    Ω→(EM1_pmap e r) ∘* loop_EM1 G ~* e :=
  begin
    fapply phomotopy.mk,
    { intro g, refine !idp_con ⬝ elim_pth r g },
    { apply is_set.elim }
  end

  definition EM1_pequiv'.{u} {G : Group.{u}} {X : pType.{u}} (e : G ≃* Ω X)
    (r : Πg h, e (g * h) = e g ⬝ e h) [is_conn 0 X] [is_trunc 1 X] : EM1 G ≃* X :=
  begin
    apply pequiv_of_pmap (EM1_pmap e r),
    apply whitehead_principle_pointed 1,
    intro k, cases k with k,
    { apply @is_equiv_of_is_contr,
      all_goals (esimp; exact _)},
    { cases k with k,
      { apply is_equiv_trunc_functor, esimp,
        apply is_equiv.homotopy_closed, rotate 1,
        { symmetry, exact phomotopy_pinv_right_of_phomotopy (loop_EM1_pmap _ _) },
        apply is_equiv_compose e },
      { apply @is_equiv_of_is_contr,
        do 2 exact trivial_homotopy_group_of_is_trunc _ (succ_lt_succ !zero_lt_succ)}}
  end

  definition EM1_pequiv.{u} {G : Group.{u}} {X : pType.{u}} (e : G ≃g π₁ X)
    [is_conn 0 X] [is_trunc 1 X] : EM1 G ≃* X :=
  begin
    apply EM1_pequiv' (pequiv_of_isomorphism e ⬝e* ptrunc_pequiv 0 (Ω X)),
    refine is_equiv.preserve_binary_of_inv_preserve _ mul concat _,
    intro p q,
    exact to_respect_mul e⁻¹ᵍ (tr p) (tr q)
  end

  definition EM1_pequiv_type (X : Type*) [is_conn 0 X] [is_trunc 1 X] : EM1 (π₁ X) ≃* X :=
  EM1_pequiv !isomorphism.refl

end EM

open hopf susp
namespace EM
  /- EM1 G is an h-space if G is an abelian group. This allows us to construct K(G,n) for n ≥ 2 -/
  variables {G : AbGroup} (n : ℕ)

  definition EM1_mul [unfold 2 3] (x x' : EM1' G) : EM1' G :=
  begin
    induction x,
    { exact x'},
    { induction x' using EM.set_rec,
      { exact pth g},
      { exact abstract begin apply loop_pathover, apply square_of_eq,
          refine !resp_mul⁻¹ ⬝ _ ⬝ !resp_mul,
          exact ap pth !mul.comm end end}},
    { refine EM.prop_rec _ x', apply resp_mul }
  end

  variable (G)
  definition EM1_mul_one (x : EM1' G) : EM1_mul x base = x :=
  begin
    induction x using EM.set_rec,
    { reflexivity},
    { apply eq_pathover_id_right, apply hdeg_square, refine EM.elim_pth _ g}
  end

  definition h_space_EM1 [constructor] [instance] : h_space (EM1' G) :=
  begin
    fapply h_space.mk,
    { exact EM1_mul},
    { exact base},
    { intro x', reflexivity},
    { apply EM1_mul_one}
  end

  /- K(G, n+1) -/
  definition EMadd1 : ℕ → Type*
  | 0 := EM1 G
  | (n+1) := ptrunc (n+2) (psusp (EMadd1 n))

  definition EMadd1_succ [unfold_full] (n : ℕ) :
    EMadd1 G (succ n) = ptrunc (n.+2) (psusp (EMadd1 G n)) :=
  idp

  definition loop_EM2 : Ω[1] (EMadd1 G 1) ≃* EM1 G :=
  hopf.delooping (EM1' G) idp

  definition is_conn_EMadd1 [instance] (n : ℕ) : is_conn n (EMadd1 G n) :=
  begin
    induction n with n IH,
    { apply is_conn_EM1 },
    { rewrite EMadd1_succ, esimp, exact _ }
  end

  definition is_trunc_EMadd1 [instance] (n : ℕ) : is_trunc (n+1) (EMadd1 G n) :=
  begin
    cases n with n,
    { apply is_trunc_EM1 },
    { apply is_trunc_trunc }
  end

  /- loops of an EM-space -/
  definition loop_EMadd1 (n : ℕ) : EMadd1 G n ≃* Ω (EMadd1 G (succ n))  :=
  begin
    cases n with n,
    { exact !loop_EM2⁻¹ᵉ* },
    { rewrite [EMadd1_succ G (succ n)],
      refine (ptrunc_pequiv (succ n + 1) _)⁻¹ᵉ*  ⬝e* _ ⬝e* (loop_ptrunc_pequiv _ _)⁻¹ᵉ*,
      have succ n + 1 ≤ 2 * succ n, from add_mul_le_mul_add n 1 1,
      refine freudenthal_pequiv _ this }
  end

  definition loopn_EMadd1_pequiv_EM1 (G : AbGroup) (n : ℕ) : EM1 G ≃* Ω[n] (EMadd1 G n) :=
  begin
    induction n with n e,
    { reflexivity },
    { refine _ ⬝e* !loopn_succ_in⁻¹ᵉ*,
      refine _ ⬝e* loopn_pequiv_loopn n !loop_EMadd1,
      exact e }
  end

  -- use loopn_EMadd1_pequiv_EM1 in this definition?
  definition loopn_EMadd1 (G : AbGroup) (n : ℕ) : G ≃* Ω[succ n] (EMadd1 G n) :=
  begin
    induction n with n e,
    { apply loop_EM1 },
    { refine _ ⬝e* !loopn_succ_in⁻¹ᵉ*,
      refine _ ⬝e* loopn_pequiv_loopn (succ n) !loop_EMadd1,
      exact e }
  end

  definition loopn_EMadd1_succ [unfold_full] (G : AbGroup) (n : ℕ) : loopn_EMadd1 G (succ n) ~*
    !loopn_succ_in⁻¹ᵉ* ∘* apn (succ n) !loop_EMadd1 ∘* loopn_EMadd1 G n :=
  by reflexivity

  definition EM_up {G : AbGroup} {X : Type*} {n : ℕ} (e : Ω[succ (succ n)] X ≃* G)
    : Ω[succ n] (Ω X) ≃* G :=
  !loopn_succ_in⁻¹ᵉ* ⬝e* e

  definition is_homomorphism_EM_up {G : AbGroup} {X : Type*} {n : ℕ}
    (e : Ω[succ (succ n)] X ≃* G)
    (r : Π(p q : Ω[succ (succ n)] X), e (p ⬝ q) = e p * e q)
    (p q : Ω[succ n] (Ω X)) : EM_up e (p ⬝ q) = EM_up e p * EM_up e q :=
  begin
    refine _ ⬝ !r, apply ap e, esimp, apply apn_con
  end

  definition EMadd1_pmap [unfold 8] {G : AbGroup} {X : Type*} (n : ℕ)
    (e : Ω[succ n] X ≃* G)
    (r : Πp q, e (p ⬝ q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n →* X :=
  begin
    revert X e r H1 H2, induction n with n f: intro X e r H1 H2,
    { exact EM1_pmap e⁻¹ᵉ* (equiv.inv_preserve_binary e concat mul r) },
    rewrite [EMadd1_succ],
    exact ptrunc.elim ((succ n).+1)
            (psusp.elim (f _ (EM_up e) (is_homomorphism_EM_up e r) _ _)),
  end

  definition EMadd1_pmap_succ {G : AbGroup} {X : Type*} (n : ℕ) (e : Ω[succ (succ n)] X ≃* G)
    r [H1 : is_conn (succ n) X] [H2 : is_trunc ((succ n).+1) X] : EMadd1_pmap (succ n) e r =
    ptrunc.elim ((succ n).+1) (psusp.elim (EMadd1_pmap n (EM_up e) (is_homomorphism_EM_up e r))) :=
  by reflexivity

  definition loop_EMadd1_pmap {G : AbGroup} {X : Type*} {n : ℕ} (e : Ω[succ (succ n)] X ≃* G)
    (r : Πp q, e (p ⬝ q) = e p * e q)
    [H1 : is_conn (succ n) X] [H2 : is_trunc ((succ n).+1) X] :
    Ω→(EMadd1_pmap (succ n) e r) ∘* loop_EMadd1 G n ~*
    EMadd1_pmap n (EM_up e) (is_homomorphism_EM_up e r) :=
  begin
    cases n with n,
    { apply hopf_delooping_elim },
    { refine !passoc⁻¹* ⬝* _,
      rewrite [EMadd1_pmap_succ (succ n)],
      refine pwhisker_right _ !ap1_ptrunc_elim ⬝* _,
      refine !passoc⁻¹* ⬝* _,
      refine pwhisker_right _ (ptrunc_elim_freudenthal_pequiv
                                (succ n) (succ (succ n)) (add_mul_le_mul_add n 1 1) _) ⬝* _,
      reflexivity }
  end

  definition loopn_EMadd1_pmap' {G : AbGroup} {X : Type*} {n : ℕ} (e : Ω[succ n] X ≃* G)
    (r : Πp q, e (p ⬝ q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] :
    Ω→[succ n](EMadd1_pmap n e r) ∘* loopn_EMadd1 G n ~* e⁻¹ᵉ* :=
  begin
    revert X e r H1 H2, induction n with n IH: intro X e r H1 H2,
    { apply loop_EM1_pmap },
    refine pwhisker_left _ !loopn_EMadd1_succ ⬝* _,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !loopn_succ_in_inv_natural ⬝* _,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (!passoc⁻¹* ⬝*
             pwhisker_right _ (!apn_pcompose⁻¹* ⬝* apn_phomotopy _ !loop_EMadd1_pmap) ⬝*
             !IH ⬝* !pinv_trans_pinv_left) ⬝* _,
    apply pinv_pcompose_cancel_left
  end

  definition EMadd1_pequiv' {G : AbGroup} {X : Type*} (n : ℕ) (e : Ω[succ n] X ≃* G)
    (r : Π(p q : Ω[succ n] X), e (p ⬝ q) = e p * e q)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n ≃* X :=
  begin
    apply pequiv_of_pmap (EMadd1_pmap n e r),
    have is_conn 0 (EMadd1 G n), from is_conn_of_le _ (zero_le_of_nat n),
    have is_trunc (n.+1) (EMadd1 G n), from !is_trunc_EMadd1,
    refine whitehead_principle_pointed (n.+1) _ _,
    intro k, apply @nat.lt_by_cases k (succ n): intro H,
    { apply @is_equiv_of_is_contr,
      do 2 exact trivial_homotopy_group_of_is_conn _ (le_of_lt_succ H)},
    { cases H, esimp, apply is_equiv_trunc_functor, esimp,
      apply is_equiv.homotopy_closed, rotate 1,
      { symmetry, exact phomotopy_pinv_right_of_phomotopy (loopn_EMadd1_pmap' _ _) },
      apply is_equiv_compose (e⁻¹ᵉ*)},
    { apply @is_equiv_of_is_contr,
      do 2 exact trivial_homotopy_group_of_is_trunc _ H}
  end

  definition EMadd1_pequiv {G : AbGroup} {X : Type*} (n : ℕ) (e : πg[n+1] X ≃g G)
    [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n ≃* X :=
  begin
    have is_set (Ω[succ n] X), from !is_set_loopn,
    apply EMadd1_pequiv' n ((ptrunc_pequiv _ _)⁻¹ᵉ* ⬝e* pequiv_of_isomorphism e),
    intro p q, esimp, exact to_respect_mul e (tr p) (tr q)
  end

  definition EMadd1_pequiv_succ {G : AbGroup} {X : Type*} (n : ℕ) (e : πag[n+2] X ≃g G)
    [H1 : is_conn (n.+1) X] [H2 : is_trunc (n.+2) X] : EMadd1 G (succ n) ≃* X :=
  EMadd1_pequiv (succ n) e

  definition ghomotopy_group_EMadd1 (n : ℕ) : πg[n+1] (EMadd1 G n) ≃g G :=
  begin
    change π₁ (Ω[n] (EMadd1 G n)) ≃g G,
    refine homotopy_group_isomorphism_of_pequiv 0 (loopn_EMadd1_pequiv_EM1 G n)⁻¹ᵉ* ⬝g _,
    apply fundamental_group_EM1,
  end

  definition EMadd1_pequiv_type (X : Type*) (n : ℕ) [is_conn (n+1) X] [is_trunc (n+1+1) X]
    : EMadd1 (πag[n+2] X) (succ n) ≃* X :=
  EMadd1_pequiv_succ n !isomorphism.refl

  /- K(G, n) -/
  definition EM (G : AbGroup) : ℕ → Type*
  | 0     := G
  | (k+1) := EMadd1 G k

  namespace ops
    abbreviation K := @EM
  end ops
  open ops

  definition homotopy_group_EM (n : ℕ) : π[n] (EM G n) ≃* G :=
  begin
    cases n with n,
    { rexact ptrunc_pequiv 0 (G) },
    { exact pequiv_of_isomorphism (ghomotopy_group_EMadd1 G n)}
  end

  definition ghomotopy_group_EM (n : ℕ) : πg[n+1] (EM G (n+1)) ≃g G :=
  ghomotopy_group_EMadd1 G n

  definition is_conn_EM [instance] (n : ℕ) : is_conn (n.-1) (EM G n) :=
  begin
    cases n with n,
    { apply is_conn_minus_one, apply tr, unfold [EM], exact 1},
    { apply is_conn_EMadd1}
  end

  definition is_conn_EM_succ [instance] (n : ℕ) : is_conn n (EM G (succ n)) :=
  is_conn_EM G (succ n)

  definition is_trunc_EM [instance] (n : ℕ) : is_trunc n (EM G n) :=
  begin
    cases n with n,
    { unfold [EM], apply semigroup.is_set_carrier},
    { apply is_trunc_EMadd1}
  end

  definition loop_EM (n : ℕ) : Ω (K G (succ n)) ≃* K G n :=
  begin
    cases n with n,
    { refine _ ⬝e* pequiv_of_isomorphism (fundamental_group_EM1 G),
      symmetry, apply ptrunc_pequiv },
    { exact !loop_EMadd1⁻¹ᵉ* }
  end

  open circle int
  definition EM_pequiv_circle : K agℤ 1 ≃* S¹* :=
  EM1_pequiv fundamental_group_of_circle⁻¹ᵍ

  /- Functorial action of Eilenberg-Maclane spaces -/

  definition EM1_functor [constructor] {G H : Group} (φ : G →g H) : EM1 G →* EM1 H :=
  begin
    fconstructor,
    { intro g, induction g,
      { exact base },
      { exact pth (φ g) },
      { exact ap pth (to_respect_mul φ g h) ⬝ resp_mul (φ g) (φ h) }},
    { reflexivity }
  end

  definition EMadd1_functor [constructor] {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    EMadd1 G n →* EMadd1 H n :=
  begin
    induction n with n ψ,
    { exact EM1_functor φ },
    { apply ptrunc_functor, apply psusp_functor, exact ψ }
  end

  definition EM_functor [unfold 4] {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    K G n →* K H n :=
  begin
    cases n with n,
    { exact pmap_of_homomorphism φ },
    { exact EMadd1_functor φ n }
  end

  -- TODO: (K G n →* K H n) ≃ (G →g H)

  /- Equivalence of Groups and pointed connected 1-truncated types -/

  definition ptruncconntype10_pequiv (X Y : 1-Type*[0]) (e : π₁ X ≃g π₁ Y) : X ≃* Y :=
  (EM1_pequiv !isomorphism.refl)⁻¹ᵉ* ⬝e* EM1_pequiv e

  definition EM1_pequiv_ptruncconntype10 (X : 1-Type*[0]) : EM1 (π₁ X) ≃* X :=
  EM1_pequiv_type X

  definition Group_equiv_ptruncconntype10 [constructor] : Group ≃ 1-Type*[0] :=
  equiv.MK (λG, ptruncconntype.mk (EM1 G) _ pt !is_conn_EM1)
           (λX, π₁ X)
           begin intro X, apply ptruncconntype_eq, esimp, exact EM1_pequiv_type X end
           begin intro G, apply eq_of_isomorphism, apply fundamental_group_EM1 end

  /- Equivalence of AbGroups and pointed n-connected (n+1)-truncated types (n ≥ 1) -/

  open trunc_index
  definition ptruncconntype_pequiv : Π(n : ℕ) (X Y : (n.+1)-Type*[n])
    (e : πg[n+1] X ≃g πg[n+1] Y), X ≃* Y
  | 0 X Y e := ptruncconntype10_pequiv X Y e
  | (succ n) X Y e :=
  begin
    refine (EMadd1_pequiv_succ n _)⁻¹ᵉ* ⬝e* EMadd1_pequiv_succ n !isomorphism.refl,
    exact e
  end

  definition EM1_pequiv_ptruncconntype (n : ℕ) (X : (n+1+1)-Type*[n+1]) :
    EMadd1 (πag[n+2] X) (succ n) ≃* X :=
  EMadd1_pequiv_type X n

  definition AbGroup_equiv_ptruncconntype' [constructor] (n : ℕ) :
    AbGroup ≃ (n + 1 + 1)-Type*[n+1] :=
  equiv.MK
    (λG, ptruncconntype.mk (EMadd1 G (n+1)) _ pt _)
    (λX, πag[n+2] X)
    begin intro X, apply ptruncconntype_eq, apply EMadd1_pequiv_type end
    begin intro G, apply AbGroup_eq_of_isomorphism, exact ghomotopy_group_EMadd1 G (n+1) end

  definition AbGroup_equiv_ptruncconntype [constructor] (n : ℕ) :
    AbGroup ≃ (n.+2)-Type*[n.+1] :=
  AbGroup_equiv_ptruncconntype' n

end EM
