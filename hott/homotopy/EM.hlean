/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Eilenberg MacLane spaces
-/

import hit.groupoid_quotient .hopf .freudenthal .homotopy_group
open algebra pointed nat eq category group algebra is_trunc iso pointed unit trunc equiv is_conn
     function is_equiv

namespace EM
  open groupoid_quotient

  variable {G : Group}
  definition EM1 (G : Group) : Type :=
  groupoid_quotient (Groupoid_of_Group G)
  definition pEM1 [constructor] (G : Group) : Type* :=
  pointed.MK (EM1 G) (elt star)

  definition base : EM1 G := elt star
  definition pth : G → base = base := pth
  definition resp_mul (g h : G) : pth (g * h) = pth g ⬝ pth h := resp_comp h g
  definition resp_one : pth (1 : G) = idp :=
  resp_id star

  definition resp_inv (g : G) : pth (g⁻¹) = (pth g)⁻¹ :=
  resp_inv g

  local attribute pointed.MK pointed.carrier pEM1 EM1 [reducible]
  protected definition rec {P : EM1 G → Type} [H : Π(x : EM1 G), is_trunc 1 (P x)]
    (Pb : P base) (Pp : Π(g : G), Pb =[pth g] Pb)
    (Pmul : Π(g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g ⬝o Pp h) (x : EM1 G) : P x :=
  begin
    induction x,
    { induction g, exact Pb},
    { induction a, induction b, exact Pp f},
    { induction a, induction b, induction c, exact Pmul f g}
  end

  protected definition rec_on {P : EM1 G → Type} [H : Π(x : EM1 G), is_trunc 1 (P x)]
    (x : EM1 G) (Pb : P base) (Pp : Π(g : G), Pb =[pth g] Pb)
    (Pmul : Π(g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g ⬝o Pp h) : P x :=
  EM.rec Pb Pp Pmul x

  protected definition set_rec {P : EM1 G → Type} [H : Π(x : EM1 G), is_set (P x)]
    (Pb : P base) (Pp : Π(g : G), Pb =[pth g] Pb) (x : EM1 G) : P x :=
  EM.rec Pb Pp !center x

  protected definition prop_rec {P : EM1 G → Type} [H : Π(x : EM1 G), is_prop (P x)]
    (Pb : P base) (x : EM1 G) : P x :=
  EM.rec Pb !center !center x

  definition rec_pth {P : EM1 G → Type} [H : Π(x : EM1 G), is_trunc 1 (P x)]
    {Pb : P base} {Pp : Π(g : G), Pb =[pth g] Pb}
    (Pmul : Π(g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g ⬝o Pp h)
    (g : G) : apd (EM.rec Pb Pp Pmul) (pth g) = Pp g :=
  proof !rec_pth qed

  protected definition elim {P : Type} [is_trunc 1 P] (Pb : P) (Pp : Π(g : G), Pb = Pb)
    (Pmul : Π(g h : G), Pp (g * h) = Pp g ⬝ Pp h) (x : EM1 G) : P :=
  begin
    induction x,
    { exact Pb},
    { exact Pp f},
    { exact Pmul f g}
  end

  protected definition elim_on [reducible] {P : Type} [is_trunc 1 P] (x : EM1 G)
    (Pb : P) (Pp : G → Pb = Pb) (Pmul : Π(g h : G), Pp (g * h) = Pp g ⬝ Pp h) : P :=
  EM.elim Pb Pp Pmul x

  protected definition set_elim [reducible] {P : Type} [is_set P] (Pb : P) (Pp : G → Pb = Pb)
    (x : EM1 G) : P :=
  EM.elim Pb Pp !center x

  protected definition prop_elim [reducible] {P : Type} [is_prop P] (Pb : P) (x : EM1 G) : P :=
  EM.elim Pb !center !center x

  definition elim_pth {P : Type} [is_trunc 1 P] {Pb : P} {Pp : G → Pb = Pb}
    (Pmul : Π(g h : G), Pp (g * h) = Pp g ⬝ Pp h) (g : G) : ap (EM.elim Pb Pp Pmul) (pth g) = Pp g :=
  proof !elim_pth qed

  protected definition elim_set.{u} (Pb : Set.{u}) (Pp : Π(g : G), Pb ≃ Pb)
    (Pmul : Π(g h : G) (x : Pb), Pp (g * h) x = Pp h (Pp g x)) (x : EM1 G) : Set.{u} :=
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

  definition base_eq_base_equiv [constructor] (G : Group) : (base = base :> pEM1 G) ≃ G :=
  !elt_eq_elt_equiv

  definition fundamental_group_pEM1 (G : Group) : π₁ (pEM1 G) ≃g G :=
  begin
    fapply isomorphism_of_equiv,
    { exact trunc_equiv_trunc 0 !base_eq_base_equiv ⬝e trunc_equiv 0 G},
    { intros g h, induction g with p, induction h with q,
      exact encode_con p q}
  end

  proposition is_trunc_pEM1 [instance] (G : Group) : is_trunc 1 (pEM1 G) :=
  !is_trunc_groupoid_quotient

  proposition is_trunc_EM1 [instance] (G : Group) : is_trunc 1 (EM1 G) :=
  !is_trunc_groupoid_quotient

  proposition is_conn_EM1 [instance] (G : Group) : is_conn 0 (EM1 G) :=
  by apply @is_conn_groupoid_quotient; esimp; exact _

  proposition is_conn_pEM1 [instance] (G : Group) : is_conn 0 (pEM1 G) :=
  is_conn_EM1 G

  definition EM1_map [unfold 7] {G : Group} {X : Type*} (e : Ω X ≃ G)
    (r : Πp q, e (p ⬝ q) = e p * e q) [is_conn 0 X] [is_trunc 1 X] : EM1 G → X :=
  begin
    intro x, induction x using EM.elim,
    { exact Point X},
    { exact e⁻¹ᵉ g},
    { exact inv_preserve_binary e concat mul r g h}
  end

end EM

open hopf susp
namespace EM
  -- The K(G,n+1):
  variables (G : CommGroup) (n : ℕ)

  definition EM1_mul [unfold 2 3] {G : CommGroup} (x x' : EM1 G) : EM1 G :=
  begin
    induction x,
    { exact x'},
    { induction x' using EM.set_rec,
      { exact pth g},
      { exact abstract begin apply loop_pathover, apply square_of_eq,
          refine !resp_mul⁻¹ ⬝ _ ⬝ !resp_mul,
          exact ap pth !mul.comm end end}},
    { refine EM.prop_rec _ x', apply resp_mul}
  end

  definition EM1_mul_one (G : CommGroup) (x : EM1 G) : EM1_mul x base = x :=
  begin
    induction x using EM.set_rec,
    { reflexivity},
    { apply eq_pathover_id_right, apply hdeg_square, refine EM.elim_pth _ g}
  end

  definition h_space_EM1 [constructor] [instance] (G : CommGroup) : h_space (pEM1 G) :=
  begin
    fapply h_space.mk,
    { exact EM1_mul},
    { exact base},
    { intro x', reflexivity},
    { apply EM1_mul_one}
  end

  /- K(G, n+1) -/
  definition EMadd1 (G : CommGroup) (n : ℕ) : Type* :=
  ptrunc (n+1) (iterate_psusp n (pEM1 G))

  definition loop_EM2 (G : CommGroup) : Ω[1] (EMadd1 G 1) ≃* pEM1 G :=
  begin
    apply hopf.delooping, reflexivity
  end

  definition homotopy_group_EM2 (G : CommGroup) : πg[1+1] (EMadd1 G 1) ≃g G :=
  begin
    refine ghomotopy_group_succ_in _ 0 ⬝g _,
    refine homotopy_group_isomorphism_of_pequiv 0 (loop_EM2 G) ⬝g _,
    apply fundamental_group_pEM1
  end

  definition homotopy_group_EMadd1 (G : CommGroup) (n : ℕ) : πg[n+1] (EMadd1 G n) ≃g G :=
  begin
    cases n with n,
    { refine homotopy_group_isomorphism_of_pequiv 0 _ ⬝g fundamental_group_pEM1 G,
      apply ptrunc_pequiv, apply is_trunc_pEM1},
    induction n with n IH,
    { apply homotopy_group_EM2 G},
    refine _ ⬝g IH,
    refine !ghomotopy_group_ptrunc ⬝g _ ⬝g !ghomotopy_group_ptrunc⁻¹ᵍ,
    apply iterate_psusp_stability_isomorphism,
    rexact add_mul_le_mul_add n 1 1
  end

  section
    local attribute EMadd1 [reducible]
    definition is_conn_EMadd1 [instance] (G : CommGroup) (n : ℕ) : is_conn n (EMadd1 G n) := _

    definition is_trunc_EMadd1 [instance] (G : CommGroup) (n : ℕ) : is_trunc (n+1) (EMadd1 G n) := _
  end

  /- K(G, n) -/
  definition EM (G : CommGroup) : ℕ → Type*
  | 0     := pType_of_Group G
  | (k+1) := EMadd1 G k

  namespace ops
    abbreviation K := EM
  end ops
  open ops

  definition phomotopy_group_EM (G : CommGroup) (n : ℕ) : π*[n] (EM G n) ≃* pType_of_Group G :=
  begin
    cases n with n,
    { rexact ptrunc_pequiv 0 (pType_of_Group G) _},
    { apply pequiv_of_isomorphism (homotopy_group_EMadd1 G n)}
  end

  definition ghomotopy_group_EM (G : CommGroup) (n : ℕ) : πg[n+1] (EM G (n+1)) ≃g G :=
  homotopy_group_EMadd1 G n

  definition is_conn_EM [instance] (G : CommGroup) (n : ℕ) : is_conn (n.-1) (EM G n) :=
  begin
    cases n with n,
    { apply is_conn_minus_one, apply tr, unfold [EM], exact 1},
    { apply is_conn_EMadd1}
  end

  definition is_conn_EM_succ [instance] (G : CommGroup) (n : ℕ) : is_conn n (EM G (succ n)) :=
  is_conn_EM G (succ n)

  definition is_trunc_EM [instance] (G : CommGroup) (n : ℕ) : is_trunc n (EM G n) :=
  begin
    cases n with n,
    { unfold [EM], apply semigroup.is_set_carrier},
    { apply is_trunc_EMadd1}
  end

  /- Uniqueness of K(G, 1) -/
  definition pEM1_pmap [constructor] {G : Group} {X : Type*} (e : Ω X ≃ G)
    (r : Πp q, e (p ⬝ q) = e p * e q) [is_conn 0 X] [is_trunc 1 X] : pEM1 G →* X :=
  begin
    apply pmap.mk (EM1_map e r),
    reflexivity,
  end

  definition loop_pEM1 [constructor] (G : Group) : Ω (pEM1 G) ≃* pType_of_Group G :=
  pequiv_of_equiv (base_eq_base_equiv G) idp

  definition loop_pEM1_pmap {G : Group} {X : Type*} (e : Ω X ≃ G)
    (r : Πp q, e (p ⬝ q) = e p * e q) [is_conn 0 X] [is_trunc 1 X] :
    Ω→(pEM1_pmap e r) ~ e⁻¹ᵉ ∘ base_eq_base_equiv G :=
  begin
    apply homotopy_of_inv_homotopy_pre (base_eq_base_equiv G),
    intro g, exact !idp_con ⬝ !elim_pth
  end

  open trunc_index
  definition pEM1_pequiv'.{u} {G : Group.{u}} {X : pType.{u}} (e : Ω X ≃ G)
    (r : Πp q, e (p ⬝ q) = e p * e q) [is_conn 0 X] [is_trunc 1 X] : pEM1 G ≃* X :=
  begin
    apply pequiv_of_pmap (pEM1_pmap e r),
    apply whitehead_principle_pointed 1,
    intro k, cases k with k,
    { apply @is_equiv_of_is_contr,
      all_goals (esimp; exact _)},
    { cases k with k,
      { apply is_equiv_trunc_functor, esimp,
        apply is_equiv.homotopy_closed, rotate 1,
        { symmetry, exact loop_pEM1_pmap _ _},
        apply is_equiv_compose, apply to_is_equiv},
      { apply @is_equiv_of_is_contr,
        do 2 exact trivial_homotopy_group_of_is_trunc _ (succ_lt_succ !zero_lt_succ)}}
  end

  definition pEM1_pequiv.{u} {G : Group.{u}} {X : pType.{u}} (e : π₁ X ≃g G)
    [is_conn 0 X] [is_trunc 1 X] : pEM1 G ≃* X :=
  begin
    apply pEM1_pequiv' (!trunc_equiv⁻¹ᵉ ⬝e equiv_of_isomorphism e),
    intro p q, esimp, exact to_respect_mul e (tr p) (tr q)
  end

  definition pEM1_pequiv_type {X : Type*} [is_conn 0 X] [is_trunc 1 X] : pEM1 (π₁ X) ≃* X :=
  pEM1_pequiv !isomorphism.refl

  definition EM_pequiv_1.{u} {G : CommGroup.{u}} {X : pType.{u}} (e : π₁ X ≃g G)
    [is_conn 0 X] [is_trunc 1 X] : EM G 1 ≃* X :=
  begin
    refine _ ⬝e* pEM1_pequiv e,
    apply ptrunc_pequiv,
    apply is_trunc_pEM1
  end

  definition EMadd1_pequiv_pEM1 (G : CommGroup) : EMadd1 G 0 ≃* pEM1 G :=
  begin apply ptrunc_pequiv, apply is_trunc_pEM1 end

  definition EM1add1_pequiv_0.{u} {G : CommGroup.{u}} {X : pType.{u}} (e : π₁ X ≃g G)
    [is_conn 0 X] [is_trunc 1 X] : EMadd1 G 0 ≃* X :=
  EMadd1_pequiv_pEM1 G ⬝e* pEM1_pequiv e

  definition KG1_pequiv.{u} {X Y : pType.{u}} (e : π₁ X ≃g π₁ Y)
    [is_conn 0 X] [is_trunc 1 X] [is_conn 0 Y] [is_trunc 1 Y] : X ≃* Y :=
  (pEM1_pequiv e)⁻¹ᵉ* ⬝e* pEM1_pequiv !isomorphism.refl

  open circle int
  definition EM_pequiv_circle : K agℤ 1 ≃* S¹. :=
  !EMadd1_pequiv_pEM1 ⬝e* pEM1_pequiv fundamental_group_of_circle

  /- loops of EM-spaces -/
  definition loop_EMadd1 {G : CommGroup} (n : ℕ) : Ω (EMadd1 G (succ n)) ≃* EMadd1 G n :=
  begin
    cases n with n,
    { symmetry, apply EM1add1_pequiv_0, rexact homotopy_group_EMadd1 G 1,
      -- apply is_conn_loop, apply is_conn_EMadd1,
      apply is_trunc_loop, apply is_trunc_EMadd1},
    { refine loop_ptrunc_pequiv _ _ ⬝e* _,
      rewrite [add_one, succ_sub_two],
      have succ n + 1 ≤ 2 * succ n, from add_mul_le_mul_add n 1 1,
      symmetry, refine freudenthal_pequiv _ this, }
  end

  definition loop_EM (G : CommGroup) (n : ℕ) : Ω (K G (succ n)) ≃* K G n :=
  begin
    cases n with n,
    { refine _ ⬝e* pequiv_of_isomorphism (fundamental_group_pEM1 G),
      refine loop_pequiv_loop (EMadd1_pequiv_pEM1 G) ⬝e* _,
      symmetry, apply ptrunc_pequiv, exact _},
    { apply loop_EMadd1}
  end

end EM
