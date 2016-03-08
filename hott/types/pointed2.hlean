/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Ported from Coq HoTT
-/


import .equiv cubical.square

open eq is_equiv equiv pointed is_trunc

structure pequiv (A B : Type*) extends equiv A B, pmap A B

namespace pointed

  attribute pequiv._trans_of_to_pmap pequiv._trans_of_to_equiv pequiv.to_pmap pequiv.to_equiv
            [unfold 3]

  variables {A B C : Type*}

  /- pointed equivalences -/

  infix ` ≃* `:25 := pequiv
  attribute pequiv.to_pmap [coercion]
  attribute pequiv.to_is_equiv [instance]

  definition pequiv_of_pmap [constructor] (f : A →* B) (H : is_equiv f) : A ≃* B :=
  pequiv.mk f _ (respect_pt f)

  definition pequiv_of_equiv [constructor] (f : A ≃ B) (H : f pt = pt) : A ≃* B :=
  pequiv.mk f _ H

  protected definition pequiv.MK [constructor] (f : A →* B) (g : B → A)
    (gf : Πa, g (f a) = a) (fg : Πb, f (g b) = b) : A ≃* B :=
  pequiv.mk f (adjointify f g fg gf) (respect_pt f)

  definition equiv_of_pequiv [constructor] (f : A ≃* B) : A ≃ B :=
  equiv.mk f _

  definition to_pinv [constructor] (f : A ≃* B) : B →* A :=
  pmap.mk f⁻¹ ((ap f⁻¹ (respect_pt f))⁻¹ ⬝ left_inv f pt)

  /- A version of pequiv.MK with stronger conditions.
     The advantage of defining a pointed equivalence with this definition is that there is a
     pointed homotopy between the inverse of the resulting equivalence and the given pointed map g.
     This is not the case when using `pequiv.MK` (if g is a pointed map),
     that will only give an ordinary homotopy.
  -/
  protected definition pequiv.MK2 [constructor] (f : A →* B) (g : B →* A)
    (gf : g ∘* f ~* !pid) (fg : f ∘* g ~* !pid) : A ≃* B :=
  pequiv.MK f g gf fg

  definition to_pmap_pequiv_MK2 [constructor] (f : A →* B) (g : B →* A)
    (gf : g ∘* f ~* !pid) (fg : f ∘* g ~* !pid) : pequiv.MK2 f g gf fg ~* f :=
  phomotopy.mk (λb, idp) !idp_con

  definition to_pinv_pequiv_MK2 [constructor] (f : A →* B) (g : B →* A)
    (gf : g ∘* f ~* !pid) (fg : f ∘* g ~* !pid) : to_pinv (pequiv.MK2 f g gf fg) ~* g :=
  phomotopy.mk (λb, idp)
    abstract [irreducible] begin
      esimp, unfold [adjointify_left_inv'],
      note H := to_homotopy_pt gf, note H2 := to_homotopy_pt fg,
      note H3 := eq_top_of_square (natural_square_tr (to_homotopy fg) (respect_pt f)),
      rewrite [▸* at *, H, H3, H2, ap_id, - +con.assoc, ap_compose' f g, con_inv,
               - ap_inv, - +ap_con g],
      apply whisker_right, apply ap02 g,
      rewrite [ap_con, - + con.assoc, +ap_inv, +inv_con_cancel_right, con.left_inv],
    end end

  definition pua {A B : Type*} (f : A ≃* B) : A = B :=
  pType_eq (equiv_of_pequiv f) !respect_pt

  protected definition pequiv.refl [refl] [constructor] (A : Type*) : A ≃* A :=
  pequiv_of_pmap !pid !is_equiv_id

  protected definition pequiv.rfl [constructor] : A ≃* A :=
  pequiv.refl A

  protected definition pequiv.symm [symm] (f : A ≃* B) : B ≃* A :=
  pequiv_of_pmap (to_pinv f) !is_equiv_inv

  protected definition pequiv.trans [trans] (f : A ≃* B) (g : B ≃* C) : A ≃* C :=
  pequiv_of_pmap (pcompose g f) !is_equiv_compose

  postfix `⁻¹ᵉ*`:(max + 1) := pequiv.symm
  infix ` ⬝e* `:75 := pequiv.trans

  definition pequiv_change_fun [constructor] (f : A ≃* B) (f' : A →* B) (Heq : f ~ f') : A ≃* B :=
  pequiv_of_pmap f' (is_equiv.homotopy_closed f Heq)

  definition pequiv_change_inv [constructor] (f : A ≃* B) (f' : B →* A) (Heq : to_pinv f ~ f')
    : A ≃* B :=
  pequiv.MK f f' (to_left_inv (equiv_change_inv f Heq)) (to_right_inv (equiv_change_inv f Heq))

  definition pequiv_rect' (f : A ≃* B) (P : A → B → Type)
    (g : Πb, P (f⁻¹ b) b) (a : A) : P a (f a) :=
  left_inv f a ▸ g (f a)

  definition pequiv_of_eq [constructor] {A B : Type*} (p : A = B) : A ≃* B :=
  pequiv_of_pmap (pcast p) !is_equiv_tr

  definition peconcat_eq {A B C : Type*} (p : A ≃* B) (q : B = C) : A ≃* C :=
  p ⬝e* pequiv_of_eq q

  definition eq_peconcat {A B C : Type*} (p : A = B) (q : B ≃* C) : A ≃* C :=
  pequiv_of_eq p ⬝e* q

  definition eq_of_pequiv {A B : Type*} (p : A ≃* B) : A = B :=
  pType_eq (equiv_of_pequiv p) !respect_pt

  definition peap {A B : Type*} (F : Type* → Type*) (p : A ≃* B) : F A ≃* F B :=
  pequiv_of_pmap (pcast (ap F (eq_of_pequiv p))) begin cases eq_of_pequiv p, apply is_equiv_id end

  definition pequiv_eq {p q : A ≃* B} (H : p = q :> (A →* B)) : p = q :=
  begin
    cases p with f Hf, cases q with g Hg, esimp at *,
    exact apd011 pequiv_of_pmap H !is_prop.elim
  end

  infix ` ⬝e*p `:75 := peconcat_eq
  infix ` ⬝pe* `:75 := eq_peconcat

  local attribute pequiv.symm [constructor]
  definition pleft_inv (f : A ≃* B) : f⁻¹ᵉ* ∘* f ~* pid A :=
  phomotopy.mk (left_inv f)
    abstract begin
      esimp, symmetry, apply con_inv_cancel_left
    end end

  definition pright_inv (f : A ≃* B) : f ∘* f⁻¹ᵉ* ~* pid B :=
  phomotopy.mk (right_inv f)
    abstract begin
      induction f with f H p, esimp,
      rewrite [ap_con, +ap_inv, -adj f, -ap_compose],
      note q := natural_square (right_inv f) p,
      rewrite [ap_id at q],
      apply eq_bot_of_square,
      exact transpose q
    end end

  definition pcancel_left (f : B ≃* C) {g h : A →* B} (p : f ∘* g ~* f ∘* h) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_left f⁻¹ᵉ* p ⬝* _:
    refine !passoc⁻¹* ⬝* _:
    refine pwhisker_right _ (pleft_inv f) ⬝* _:
    apply pid_comp
  end


  definition pcancel_right (f : A ≃* B) {g h : B →* C} (p : g ∘* f ~* h ∘* f) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_right f⁻¹ᵉ* p ⬝* _:
    refine !passoc ⬝* _:
    refine pwhisker_left _ (pright_inv f) ⬝* _:
    apply comp_pid
  end

  definition phomotopy_pinv_right_of_phomotopy {f : A ≃* B} {g : B →* C} {h : A →* C}
    (p : g ∘* f ~* h) : g ~* h ∘* f⁻¹ᵉ* :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pright_inv f) ⬝* _,
    apply comp_pid
  end

  definition phomotopy_of_pinv_right_phomotopy {f : B ≃* A} {g : B →* C} {h : A →* C}
    (p : g ∘* f⁻¹ᵉ* ~* h) : g ~* h ∘* f :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pleft_inv f) ⬝* _,
    apply comp_pid
  end

  definition pinv_right_phomotopy_of_phomotopy {f : A ≃* B} {g : B →* C} {h : A →* C}
    (p : h ~* g ∘* f) : h ∘* f⁻¹ᵉ* ~* g :=
  (phomotopy_pinv_right_of_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_of_phomotopy_pinv_right {f : B ≃* A} {g : B →* C} {h : A →* C}
    (p : h ~* g ∘* f⁻¹ᵉ*) : h ∘* f ~* g :=
  (phomotopy_of_pinv_right_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_pinv_left_of_phomotopy {f : B ≃* C} {g : A →* B} {h : A →* C}
    (p : f ∘* g ~* h) : g ~* f⁻¹ᵉ* ∘* h :=
  begin
    refine _ ⬝* pwhisker_left _ p, symmetry,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (pleft_inv f) ⬝* _,
    apply pid_comp
  end

  definition phomotopy_of_pinv_left_phomotopy {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : f⁻¹ᵉ* ∘* g ~* h) : g ~* f ∘* h :=
  begin
    refine _ ⬝* pwhisker_left _ p, symmetry,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (pright_inv f) ⬝* _,
    apply pid_comp
  end

  definition pinv_left_phomotopy_of_phomotopy {f : B ≃* C} {g : A →* B} {h : A →* C}
    (p : h ~* f ∘* g) : f⁻¹ᵉ* ∘* h ~* g :=
  (phomotopy_pinv_left_of_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_of_phomotopy_pinv_left {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : h ~* f⁻¹ᵉ* ∘* g) : f ∘* h ~* g :=
  (phomotopy_of_pinv_left_phomotopy p⁻¹*)⁻¹*

  /- pointed equivalences between particular pointed types -/

  definition loopn_pequiv_loopn [constructor] (n : ℕ) (f : A ≃* B) : Ω[n] A ≃* Ω[n] B :=
  pequiv.MK2 (apn n f) (apn n f⁻¹ᵉ*)
  abstract begin
    induction n with n IH,
    { apply pleft_inv},
    { replace nat.succ n with n + 1,
      rewrite [+apn_succ],
      refine !ap1_compose⁻¹* ⬝* _,
      refine ap1_phomotopy IH ⬝* _,
      apply ap1_id}
  end end
  abstract begin
    induction n with n IH,
    { apply pright_inv},
    { replace nat.succ n with n + 1,
      rewrite [+apn_succ],
      refine !ap1_compose⁻¹* ⬝* _,
      refine ap1_phomotopy IH ⬝* _,
      apply ap1_id}
  end end

  definition loop_pequiv_loop [constructor] (f : A ≃* B) : Ω A ≃* Ω B :=
  loopn_pequiv_loopn 1 f

  definition to_pmap_loopn_pequiv_loopn [constructor] (n : ℕ) (f : A ≃* B)
    : loopn_pequiv_loopn n f ~* apn n f :=
  !to_pmap_pequiv_MK2

  definition to_pinv_loopn_pequiv_loopn [constructor] (n : ℕ) (f : A ≃* B)
    : (loopn_pequiv_loopn n f)⁻¹ᵉ* ~* apn n f⁻¹ᵉ* :=
  !to_pinv_pequiv_MK2

  definition loopn_pequiv_loopn_con (n : ℕ) (f : A ≃* B) (p q : Ω[n+1] A)
    : loopn_pequiv_loopn (n+1) f (p ⬝ q) =
    loopn_pequiv_loopn (n+1) f p ⬝ loopn_pequiv_loopn (n+1) f q :=
  ap1_con (loopn_pequiv_loopn n f) p q

  definition loopn_pequiv_loopn_rfl (n : ℕ) :
    loopn_pequiv_loopn n (@pequiv.refl A) = @pequiv.refl (Ω[n] A) :=
  begin
    apply pequiv_eq, apply eq_of_phomotopy,
    exact !to_pmap_loopn_pequiv_loopn ⬝* apn_pid n,
  end

  definition pmap_functor [constructor] {A A' B B' : Type*} (f : A' →* A) (g : B →* B') :
    ppmap A B →* ppmap A' B' :=
  pmap.mk (λh, g ∘* h ∘* f)
    abstract begin
      fapply pmap_eq,
      { esimp, intro a, exact respect_pt g},
      { rewrite [▸*, ap_constant], apply idp_con}
    end end

/-
  definition pmap_pequiv_pmap {A A' B B' : Type*} (f : A ≃* A') (g : B ≃* B') :
    ppmap A B ≃* ppmap A' B' :=
  pequiv.MK (pmap_functor f⁻¹ᵉ* g) (pmap_functor f g⁻¹ᵉ*)
    abstract begin
      intro a, esimp, apply pmap_eq,
      { esimp, },
      { }
    end end
    abstract begin

    end end
-/

end pointed
