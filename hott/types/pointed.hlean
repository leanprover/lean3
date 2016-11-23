/-
Copyright (c) 2014-2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
The basic definitions are in init.pointed
-/

import .nat.basic ..arity ..prop_trunc
open is_trunc eq prod sigma nat equiv option is_equiv bool unit algebra sigma.ops sum

namespace pointed
  variables {A B : Type}

  definition pointed_loop [instance] [constructor] (a : A) : pointed (a = a) :=
  pointed.mk idp

  definition pointed_fun_closed [constructor] (f : A → B) [H : pointed A] : pointed B :=
  pointed.mk (f pt)

  definition loop [reducible] [constructor] (A : Type*) : Type* :=
  pointed.mk' (point A = point A)

  definition loopn [reducible] : ℕ → Type* → Type*
  | loopn  0    X := X
  | loopn (n+1) X := loop (loopn n X)

  notation `Ω` := loop
  notation `Ω[`:95 n:0 `]`:0 := loopn n

  namespace ops
    -- this is in a separate namespace because it caused type class inference to loop in some places
    definition is_trunc_pointed_MK [instance] [priority 1100] (n : ℕ₋₂) {A : Type} (a : A)
      [H : is_trunc n A] : is_trunc n (pointed.MK A a) :=
    H
  end ops

  definition is_trunc_loop [instance] [priority 1100] (A : Type*)
    (n : ℕ₋₂) [H : is_trunc (n.+1) A] : is_trunc n (Ω A) :=
  !is_trunc_eq

  definition loopn_zero_eq [unfold_full] (A : Type*)
    : Ω[0] A = A := rfl

  definition loopn_succ_eq [unfold_full] (k : ℕ) (A : Type*)
    : Ω[succ k] A = Ω (Ω[k] A) := rfl

  definition rfln  [constructor] [reducible] {n : ℕ} {A : Type*} : Ω[n] A := pt
  definition refln [constructor] [reducible] (n : ℕ) (A : Type*) : Ω[n] A := pt
  definition refln_eq_refl [unfold_full] (A : Type*) (n : ℕ) : rfln = rfl :> Ω[succ n] A := rfl

  definition loopn_space [unfold 3] (A : Type) [H : pointed A] (n : ℕ) : Type :=
  Ω[n] (pointed.mk' A)

  definition loop_mul {k : ℕ} {A : Type*} (mul : A → A → A) : Ω[k] A → Ω[k] A → Ω[k] A :=
  begin cases k with k, exact mul, exact concat end

  definition pType_eq {A B : Type*} (f : A ≃ B) (p : f pt = pt) : A = B :=
  begin
    cases A with A a, cases B with B b, esimp at *,
    fapply apdt011 @pType.mk,
    { apply ua f},
    { rewrite [cast_ua, p]},
  end

  definition pType_eq_elim {A B : Type*} (p : A = B :> Type*)
    : Σ(p : carrier A = carrier B :> Type), Point A =[p] Point B :=
  by induction p; exact ⟨idp, idpo⟩

  protected definition pType.sigma_char.{u} : pType.{u} ≃ Σ(X : Type.{u}), X :=
  begin
    fapply equiv.MK,
    { intro x, induction x with X x, exact ⟨X, x⟩},
    { intro x, induction x with X x, exact pointed.MK X x},
    { intro x, induction x with X x, reflexivity},
    { intro x, induction x with X x, reflexivity},
  end

  definition add_point [constructor] (A : Type) : Type* :=
  pointed.Mk (none : option A)
  postfix `₊`:(max+1) := add_point
  -- the inclusion A → A₊ is called "some", the extra point "pt" or "none" ("@none A")
end pointed

namespace pointed
  /- truncated pointed types -/
  definition ptrunctype_eq {n : ℕ₋₂} {A B : n-Type*}
    (p : A = B :> Type) (q : Point A =[p] Point B) : A = B :=
  begin
    induction A with A HA a, induction B with B HB b, esimp at *,
    induction q, esimp,
    refine ap010 (ptrunctype.mk A) _ a,
    exact !is_prop.elim
  end

  definition ptrunctype_eq_of_pType_eq {n : ℕ₋₂} {A B : n-Type*} (p : A = B :> Type*)
    : A = B :=
  begin
    cases pType_eq_elim p with q r,
    exact ptrunctype_eq q r
  end

  definition is_trunc_ptrunctype [instance] {n : ℕ₋₂} (A : n-Type*) : is_trunc n A :=
  trunctype.struct A

end pointed open pointed

namespace pointed
  variables {A B C D : Type*} {f g h : A →* B}

  /- categorical properties of pointed maps -/

  definition pmap_of_map [constructor] {A B : Type} (f : A → B) (a : A) :
    pointed.MK A a →* pointed.MK B (f a) :=
  pmap.mk f idp

  definition pid [constructor] [refl] (A : Type*) : A →* A :=
  pmap.mk id idp

  definition pcompose [constructor] [trans] (g : B →* C) (f : A →* B) : A →* C :=
  pmap.mk (λa, g (f a)) (ap g (respect_pt f) ⬝ respect_pt g)

  infixr ` ∘* `:60 := pcompose

  definition passoc (h : C →* D) (g : B →* C) (f : A →* B) : (h ∘* g) ∘* f ~* h ∘* (g ∘* f) :=
  begin
    fconstructor, intro a, reflexivity,
    cases A, cases B, cases C, cases D, cases f with f pf, cases g with g pg, cases h with h ph,
    esimp at *,
    induction pf, induction pg, induction ph, reflexivity
  end

  definition pid_pcompose [constructor] (f : A →* B) : pid B ∘* f ~* f :=
  begin
    fconstructor,
    { intro a, reflexivity},
    { reflexivity}
  end

  definition pcompose_pid [constructor] (f : A →* B) : f ∘* pid A ~* f :=
  begin
    fconstructor,
    { intro a, reflexivity},
    { reflexivity}
  end

  /- equivalences and equalities -/

  definition pmap.sigma_char [constructor] {A B : Type*} : (A →* B) ≃ Σ(f : A → B), f pt = pt :=
  begin
    fapply equiv.MK : intros f,
    { exact ⟨f , respect_pt f⟩ },
    all_goals cases f with f p,
    { exact pmap.mk f p },
    all_goals reflexivity
  end

  definition pmap_eq (r : Πa, f a = g a) (s : respect_pt f = (r pt) ⬝ respect_pt g) : f = g :=
  begin
    cases f with f p, cases g with g q,
    esimp at *,
    fapply apd011 pmap.mk,
    { exact eq_of_homotopy r},
    { apply concato_eq, apply eq_pathover_Fl, apply inv_con_eq_of_eq_con,
      rewrite [ap_eq_apd10, apd10_eq_of_homotopy, s]}
  end

  definition pmap_eq_of_homotopy {A B : Type*} {f g : A →* B} [is_set B] (p : f ~ g) : f = g :=
  pmap_eq p !is_set.elim

  definition pmap_equiv_left (A : Type) (B : Type*) : A₊ →* B ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intro f a, cases f with f p, exact f (some a)},
    { intro f, fconstructor,
        intro a, cases a, exact pt, exact f a,
        reflexivity},
    { intro f, reflexivity},
    { intro f, cases f with f p, esimp, fapply pmap_eq,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹},
      { esimp, exact !con.left_inv⁻¹}},
  end

  definition pmap_equiv_right (A : Type*) (B : Type)
    : (Σ(b : B), A →* (pointed.Mk b)) ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intro u a, exact pmap.to_fun u.2 a},
    { intro f, refine ⟨f pt, _⟩, fapply pmap.mk,
        intro a, esimp, exact f a,
        reflexivity},
    { intro f, reflexivity},
    { intro u, cases u with b f, cases f with f p, esimp at *, induction p,
      reflexivity}
  end

  -- pmap_pbool_pequiv is the pointed equivalence
  definition pmap_pbool_equiv [constructor] (B : Type*) : (pbool →* B) ≃ B :=
  begin
    fapply equiv.MK,
    { intro f, cases f with f p, exact f tt},
    { intro b, fconstructor,
        intro u, cases u, exact pt, exact b,
        reflexivity},
    { intro b, reflexivity},
    { intro f, cases f with f p, esimp, fapply pmap_eq,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹},
      { esimp, exact !con.left_inv⁻¹}},
  end

  /- some specific pointed maps -/

  -- The constant pointed map between any two types
  definition pconst [constructor] (A B : Type*) : A →* B :=
  pmap.mk (λ a, Point B) idp

  -- the pointed type of pointed maps
  definition ppmap [constructor] (A B : Type*) : Type* :=
  pType.mk (A →* B) (pconst A B)

  definition pcast [constructor] {A B : Type*} (p : A = B) : A →* B :=
  pmap.mk (cast (ap pType.carrier p)) (by induction p; reflexivity)

  definition pinverse [constructor] {X : Type*} : Ω X →* Ω X :=
  pmap.mk eq.inverse idp

  definition ap1 [constructor] (f : A →* B) : Ω A →* Ω B :=
  begin
    fconstructor,
    { intro p, exact !respect_pt⁻¹ ⬝ ap f p ⬝ !respect_pt},
    { esimp, apply con.left_inv}
  end

  definition apn (n : ℕ) (f : A →* B) : Ω[n] A →* Ω[n] B :=
  begin
  induction n with n IH,
  { exact f},
  { esimp [loopn], exact ap1 IH}
  end

  prefix `Ω→`:(max+5) := ap1
  notation `Ω→[`:95 n:0 `]`:0 := apn n

  definition ptransport [constructor] {A : Type} (B : A → Type*) {a a' : A} (p : a = a')
    : B a →* B a' :=
  pmap.mk (transport B p) (apdt (λa, Point (B a)) p)

  definition pmap_of_eq_pt [constructor] {A : Type} {a a' : A} (p : a = a') :
    pointed.MK A a →* pointed.MK A a' :=
  pmap.mk id p

  definition pbool_pmap [constructor] {A : Type*} (a : A) : pbool →* A :=
  pmap.mk (bool.rec pt a) idp

  -- properties of pointed maps

  definition apn_zero [unfold_full] (f : A →* B) : Ω→[0] f = f := idp
  definition apn_succ [unfold_full] (n : ℕ) (f : A →* B) : Ω→[n + 1] f = Ω→ (Ω→[n] f) := idp

  theorem ap1_con (f : A →* B) (p q : Ω A) : ap1 f (p ⬝ q) = ap1 f p ⬝ ap1 f q :=
  begin
    rewrite [▸*,ap_con, +con.assoc, con_inv_cancel_left], repeat apply whisker_left
  end

  theorem ap1_inv (f : A →* B) (p : Ω A) : ap1 f p⁻¹ = (ap1 f p)⁻¹ :=
  begin
    rewrite [▸*,ap_inv, +con_inv, inv_inv, +con.assoc], repeat apply whisker_left
  end

  definition pinverse_con [constructor] {X : Type*} (p q : Ω X)
    : pinverse (p ⬝ q) = pinverse q ⬝ pinverse p :=
  !con_inv

  definition pinverse_inv [constructor] {X : Type*} (p : Ω X)
    : pinverse p⁻¹ = (pinverse p)⁻¹ :=
  idp

  theorem apn_con (n : ℕ) (f : A →* B) (p q : Ω[n+1] A)
    : apn (n+1) f (p ⬝ q) = apn (n+1) f p ⬝ apn (n+1) f q :=
  by rewrite [+apn_succ, ap1_con]

  theorem apn_inv (n : ℕ)  (f : A →* B) (p : Ω[n+1] A) : apn (n+1) f p⁻¹ = (apn (n+1) f p)⁻¹ :=
  by rewrite [+apn_succ, ap1_inv]

  definition is_equiv_ap1 (f : A →* B) [is_equiv f] : is_equiv (ap1 f) :=
  begin
    induction B with B b, induction f with f pf, esimp at *, cases pf, esimp,
    apply is_equiv.homotopy_closed (ap f),
    intro p, exact !idp_con⁻¹
  end

  definition is_equiv_apn (n : ℕ) (f : A →* B) [H : is_equiv f]
    : is_equiv (apn n f) :=
  begin
    induction n with n IH,
    { exact H},
    { exact is_equiv_ap1 (apn n f)}
  end

  definition is_equiv_pcast [instance] {A B : Type*} (p : A = B) : is_equiv (pcast p) :=
  !is_equiv_cast

  /- categorical properties of pointed homotopies -/

  protected definition phomotopy.refl [constructor] [refl] (f : A →* B) : f ~* f :=
  begin
    fconstructor,
    { intro a, exact idp},
    { apply idp_con}
  end

  protected definition phomotopy.rfl [constructor] {f : A →* B} : f ~* f :=
  phomotopy.refl f

  protected definition phomotopy.trans [constructor] [trans] (p : f ~* g) (q : g ~* h)
    : f ~* h :=
  phomotopy.mk (λa, p a ⬝ q a)
    abstract begin
      induction f, induction g, induction p with p p', induction q with q q', esimp at *,
      induction p', induction q', esimp, apply con.assoc
    end end

  protected definition phomotopy.symm [constructor] [symm] (p : f ~* g) : g ~* f :=
  phomotopy.mk (λa, (p a)⁻¹)
    abstract begin
      induction f, induction p with p p', esimp at *,
      induction p', esimp, apply inv_con_cancel_left
    end end

  infix ` ⬝* `:75 := phomotopy.trans
  postfix `⁻¹*`:(max+1) := phomotopy.symm

  /- equalities and equivalences relating pointed homotopies -/

  definition phomotopy.sigma_char [constructor] {A B : Type*} (f g : A →* B)
    : (f ~* g) ≃ Σ(p : f ~ g), p pt ⬝ respect_pt g = respect_pt f :=
  begin
    fapply equiv.MK : intros h,
    { exact ⟨h , to_homotopy_pt h⟩ },
    all_goals cases h with h p,
    { exact phomotopy.mk h p },
    all_goals reflexivity
  end

  definition is_trunc_pmap [instance] (n : ℕ₋₂) (A B : Type*) [is_trunc n B] :
    is_trunc n (A →* B) :=
  is_trunc_equiv_closed_rev _ !pmap.sigma_char

  definition is_trunc_ppmap [instance] (n : ℕ₋₂) {A B : Type*} [is_trunc n B] :
    is_trunc n (ppmap A B) :=
  !is_trunc_pmap

  definition phomotopy_of_eq [constructor] {A B : Type*} {f g : A →* B} (p : f = g) : f ~* g :=
  phomotopy.mk (ap010 pmap.to_fun p) begin induction p, apply idp_con end

  definition pconcat_eq [constructor] {A B : Type*} {f g h : A →* B} (p : f ~* g) (q : g = h)
    : f ~* h :=
  p ⬝* phomotopy_of_eq q

  definition eq_pconcat [constructor] {A B : Type*} {f g h : A →* B} (p : f = g) (q : g ~* h)
    : f ~* h :=
  phomotopy_of_eq p ⬝* q

  infix ` ⬝*p `:75 := pconcat_eq
  infix ` ⬝p* `:75 := eq_pconcat

  definition eq_of_phomotopy (p : f ~* g) : f = g :=
  begin
    fapply pmap_eq,
    { intro a, exact p a},
    { exact !to_homotopy_pt⁻¹}
  end

  definition pmap_eq_equiv {A B : Type*} (f g : A →* B) : (f = g) ≃ (f ~* g) :=
  calc (f = g) ≃ pmap.sigma_char f = pmap.sigma_char g
                 : eq_equiv_fn_eq pmap.sigma_char f g
          ...  ≃ Σ(p : pmap.to_fun f = pmap.to_fun g),
                   pathover (λh, h pt = pt) (respect_pt f) p (respect_pt g)
                 : sigma_eq_equiv _ _
          ...  ≃ Σ(p : pmap.to_fun f = pmap.to_fun g), respect_pt f = ap (λh, h pt) p ⬝ respect_pt g
                 : sigma_equiv_sigma_right (λp, eq_pathover_equiv_Fl p (respect_pt f)
                                                                       (respect_pt g))
          ...  ≃ Σ(p : pmap.to_fun f = pmap.to_fun g), respect_pt f = ap10 p pt ⬝ respect_pt g
                 : sigma_equiv_sigma_right
                     (λp, equiv_eq_closed_right _ (whisker_right (ap_eq_apd10 p _) _))
          ...  ≃ Σ(p : pmap.to_fun f ~ pmap.to_fun g), respect_pt f = p pt ⬝ respect_pt g
                 : sigma_equiv_sigma_left' eq_equiv_homotopy
          ...  ≃ Σ(p : pmap.to_fun f ~ pmap.to_fun g), p pt ⬝ respect_pt g = respect_pt f
                 : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
          ...  ≃ (f ~* g) : phomotopy.sigma_char f g

  /-
    Pointed maps respecting pointed homotopies.
    In general we need function extensionality for pap,
    but for particular F we can do it without function extensionality.
    This is preferred, because such pointed homotopies compute
  -/
  definition pap (F : (A →* B) → (C →* D)) {f g : A →* B} (p : f ~* g) : F f ~* F g :=
  phomotopy.mk (ap010 (λf, pmap.to_fun (F f)) (eq_of_phomotopy p))
               begin cases eq_of_phomotopy p, apply idp_con end

  definition ap1_phomotopy {f g : A →* B} (p : f ~* g)
    : ap1 f ~* ap1 g :=
  begin
    induction p with p q, induction f with f pf, induction g with g pg, induction B with B b,
    esimp at *, induction q, induction pg,
    fapply phomotopy.mk,
    { intro l, esimp, refine _ ⬝ !idp_con⁻¹, refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con,
      apply ap_con_eq_con_ap},
    { induction A with A a, unfold [ap_con_eq_con_ap], generalize p a, generalize g a, intro b q,
      induction q, reflexivity}
  end

  definition apn_phomotopy {f g : A →* B} (n : ℕ) (p : f ~* g) : apn n f ~* apn n g :=
  begin
    induction n with n IH,
    { exact p},
    { exact ap1_phomotopy IH}
  end

  /- pointed homotopies between the given pointed maps -/

  definition ap1_pid [constructor] {A : Type*} : ap1 (pid A) ~* pid (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, esimp, refine !idp_con ⬝ !ap_id},
    { reflexivity}
  end

  definition ap1_pinverse {A : Type*} : ap1 (@pinverse A) ~* @pinverse (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, esimp, refine !idp_con ⬝ _, exact !inv_eq_inv2⁻¹ },
    { reflexivity}
  end

  definition ap1_pcompose (g : B →* C) (f : A →* B) : ap1 (g ∘* f) ~* ap1 g ∘* ap1 f :=
  begin
    induction B, induction C, induction g with g pg, induction f with f pf, esimp at *,
    induction pg, induction pf,
    fconstructor,
    { intro p, esimp, apply whisker_left, exact ap_compose g f p ⬝ ap (ap g) !idp_con⁻¹},
    { reflexivity}
  end

  definition ap1_pcompose_pinverse (f : A →* B) : ap1 f ∘* pinverse ~* pinverse ∘* ap1 f :=
  begin
    fconstructor,
    { intro p, esimp, refine !con.assoc ⬝ _ ⬝ !con_inv⁻¹, apply whisker_left,
      refine whisker_right !ap_inv _ ⬝ _ ⬝ !con_inv⁻¹, apply whisker_left,
      exact !inv_inv⁻¹},
    { induction B with B b, induction f with f pf, esimp at *, induction pf, reflexivity},
  end

  definition ap1_pconst (A B : Type*) : Ω→(pconst A B) ~* pconst (Ω A) (Ω B) :=
  phomotopy.mk (λp, idp_con _ ⬝ ap_constant p pt) rfl

  definition ptransport_change_eq [constructor] {A : Type} (B : A → Type*) {a a' : A} {p q : a = a'}
    (r : p = q) : ptransport B p ~* ptransport B q :=
  phomotopy.mk (λb, ap (λp, transport B p b) r) begin induction r, apply idp_con end

  definition pnatural_square {A B : Type} (X : B → Type*) {f g : A → B}
    (h : Πa, X (f a) →* X (g a)) {a a' : A} (p : a = a') :
    h a' ∘* ptransport X (ap f p) ~* ptransport X (ap g p) ∘* h a :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹*

  definition apn_pid [constructor] {A : Type*} (n : ℕ) : apn n (pid A) ~* pid (Ω[n] A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap1_phomotopy IH ⬝* ap1_pid}
  end

  definition apn_pconst (A B : Type*) (n : ℕ) :
    apn n (pconst A B) ~* pconst (Ω[n] A) (Ω[n] B) :=
  begin
    induction n with n IH,
    { reflexivity },
    { exact ap1_phomotopy IH ⬝* !ap1_pconst }
  end

  definition apn_pcompose (n : ℕ) (g : B →* C) (f : A →* B) :
    apn n (g ∘* f) ~* apn n g ∘* apn n f :=
  begin
    induction n with n IH,
    { reflexivity},
    { refine ap1_phomotopy IH ⬝* _, apply ap1_pcompose}
  end

  definition pcast_idp [constructor] {A : Type*} : pcast (idpath A) ~* pid A :=
  by reflexivity

  definition pinverse_pinverse (A : Type*) : pinverse ∘* pinverse ~* pid (Ω A) :=
  begin
    fapply phomotopy.mk,
    { apply inv_inv},
    { reflexivity}
  end

  definition pcast_ap_loop [constructor] {A B : Type*} (p : A = B) :
    pcast (ap Ω p) ~* ap1 (pcast p) :=
  begin
    fapply phomotopy.mk,
    { intro a, induction p, esimp, exact (!idp_con ⬝ !ap_id)⁻¹},
    { induction p, reflexivity}
  end

  definition ap1_pmap_of_map [constructor] {A B : Type} (f : A → B) (a : A) :
    ap1 (pmap_of_map f a) ~* pmap_of_map (ap f) (idpath a) :=
  begin
    fapply phomotopy.mk,
    { intro a, esimp, apply idp_con},
    { reflexivity}
  end

  definition pcast_commute [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pcast (ap C p) ∘* f a₁ ~* f a₂ ∘* pcast (ap B p) :=
  phomotopy.mk
    begin induction p, reflexivity end
    begin induction p, esimp, refine !idp_con ⬝ !idp_con ⬝ !ap_id⁻¹ end

  /- pointed equivalences -/

  /- constructors / projections + variants -/
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

  definition to_pmap_pequiv_of_pmap {A B : Type*} (f : A →* B) (H : is_equiv f)
    : pequiv.to_pmap (pequiv_of_pmap f H) = f :=
  by cases f; reflexivity

  /-
     A version of pequiv.MK with stronger conditions.
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
      esimp,
      note H := to_homotopy_pt gf, note H2 := to_homotopy_pt fg,
      note H3 := eq_top_of_square (natural_square (to_homotopy fg) (respect_pt f)),
      rewrite [▸* at *, H, H3, H2, ap_id, - +con.assoc, ap_compose' f g, con_inv,
               - ap_inv, - +ap_con g],
      apply whisker_right, apply ap02 g,
      rewrite [ap_con, - + con.assoc, +ap_inv, +inv_con_cancel_right, con.left_inv],
    end end

  /- categorical properties of pointed equivalences -/

  protected definition pequiv.refl [refl] [constructor] (A : Type*) : A ≃* A :=
  pequiv_of_pmap !pid !is_equiv_id

  protected definition pequiv.rfl [constructor] : A ≃* A :=
  pequiv.refl A

  protected definition pequiv.symm [symm] [constructor] (f : A ≃* B) : B ≃* A :=
  pequiv_of_pmap (to_pinv f) !is_equiv_inv

  protected definition pequiv.trans [trans] [constructor] (f : A ≃* B) (g : B ≃* C) : A ≃* C :=
  pequiv_of_pmap (g ∘* f) !is_equiv_compose

  definition pequiv_compose {A B C : Type*} (g : B ≃* C) (f : A ≃* B) : A ≃* C :=
  pequiv_of_pmap (g ∘* f) (is_equiv_compose g f)

  infixr ` ∘*ᵉ `:60 := pequiv_compose
  postfix `⁻¹ᵉ*`:(max + 1) := pequiv.symm
  infix ` ⬝e* `:75 := pequiv.trans

  /- more on pointed equivalences -/

  definition pequiv_ap [constructor] {A : Type} (B : A → Type*) {a a' : A} (p : a = a')
    : B a ≃* B a' :=
  pequiv_of_pmap (ptransport B p) !is_equiv_tr

  definition to_pmap_pequiv_trans {A B C : Type*} (f : A ≃* B) (g : B ≃* C)
    : pequiv.to_pmap (f ⬝e* g) = g ∘* f :=
  !to_pmap_pequiv_of_pmap

  definition pequiv_change_fun [constructor] (f : A ≃* B) (f' : A →* B) (Heq : f ~ f') : A ≃* B :=
  pequiv_of_pmap f' (is_equiv.homotopy_closed f Heq)

  definition pequiv_change_inv [constructor] (f : A ≃* B) (f' : B →* A) (Heq : to_pinv f ~ f')
    : A ≃* B :=
  pequiv.MK f f' (to_left_inv (equiv_change_inv f Heq)) (to_right_inv (equiv_change_inv f Heq))

  definition pequiv_rect' (f : A ≃* B) (P : A → B → Type)
    (g : Πb, P (f⁻¹ b) b) (a : A) : P a (f a) :=
  left_inv f a ▸ g (f a)

  definition pua {A B : Type*} (f : A ≃* B) : A = B :=
  pType_eq (equiv_of_pequiv f) !respect_pt

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

  infix ` ⬝e*p `:75 := peconcat_eq
  infix ` ⬝pe* `:75 := eq_peconcat

  definition pequiv_of_eq_commute [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pequiv_of_eq (ap C p) ∘* f a₁ ~* f a₂ ∘* pequiv_of_eq (ap B p) :=
  pcast_commute f p

  /-
    the theorem pequiv_eq, which gives a condition for two pointed equivalences are equal
    is in types.equiv to avoid circular imports
  -/

  /- computation rules of pointed homotopies, possibly combined with pointed equivalences -/
  definition pwhisker_left [constructor] (h : B →* C) (p : f ~* g) : h ∘* f ~* h ∘* g :=
  phomotopy.mk (λa, ap h (p a))
    abstract begin
      induction A, induction B, induction C,
      induction f with f pf, induction g with g pg, induction h with h ph,
      induction p with p p', esimp at *, induction ph, induction pg, induction p', reflexivity
    end end

  definition pwhisker_right [constructor] (h : C →* A) (p : f ~* g) : f ∘* h ~* g ∘* h :=
  phomotopy.mk (λa, p (h a))
    abstract begin
      induction A, induction B, induction C,
      induction f with f pf, induction g with g pg, induction h with h ph,
      induction p with p p', esimp at *, induction ph, induction pg, induction p', esimp,
      exact !idp_con⁻¹
    end end

  definition pconcat2 [constructor] {A B C : Type*} {h i : B →* C} {f g : A →* B}
    (q : h ~* i) (p : f ~* g) : h ∘* f ~* i ∘* g :=
  pwhisker_left _ p ⬝* pwhisker_right _ q

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
      exact q
    end end

  definition pcancel_left (f : B ≃* C) {g h : A →* B} (p : f ∘* g ~* f ∘* h) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_left f⁻¹ᵉ* p ⬝* _:
    refine !passoc⁻¹* ⬝* _:
    refine pwhisker_right _ (pleft_inv f) ⬝* _:
    apply pid_pcompose
  end

  definition pcancel_right (f : A ≃* B) {g h : B →* C} (p : g ∘* f ~* h ∘* f) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_right f⁻¹ᵉ* p ⬝* _:
    refine !passoc ⬝* _:
    refine pwhisker_left _ (pright_inv f) ⬝* _:
    apply pcompose_pid
  end

  definition phomotopy_pinv_right_of_phomotopy {f : A ≃* B} {g : B →* C} {h : A →* C}
    (p : g ∘* f ~* h) : g ~* h ∘* f⁻¹ᵉ* :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pright_inv f) ⬝* _,
    apply pcompose_pid
  end

  definition phomotopy_of_pinv_right_phomotopy {f : B ≃* A} {g : B →* C} {h : A →* C}
    (p : g ∘* f⁻¹ᵉ* ~* h) : g ~* h ∘* f :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pleft_inv f) ⬝* _,
    apply pcompose_pid
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
    apply pid_pcompose
  end

  definition phomotopy_of_pinv_left_phomotopy {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : f⁻¹ᵉ* ∘* g ~* h) : g ~* f ∘* h :=
  begin
    refine _ ⬝* pwhisker_left _ p, symmetry,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (pright_inv f) ⬝* _,
    apply pid_pcompose
  end

  definition pinv_left_phomotopy_of_phomotopy {f : B ≃* C} {g : A →* B} {h : A →* C}
    (p : h ~* f ∘* g) : f⁻¹ᵉ* ∘* h ~* g :=
  (phomotopy_pinv_left_of_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_of_phomotopy_pinv_left {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : h ~* f⁻¹ᵉ* ∘* g) : f ∘* h ~* g :=
  (phomotopy_of_pinv_left_phomotopy p⁻¹*)⁻¹*

  definition pcompose2 {A B C : Type*} {g g' : B →* C} {f f' : A →* B} (p : f ~* f') (q : g ~* g') :
    g ∘* f ~* g' ∘* f' :=
  pwhisker_right f q ⬝* pwhisker_left g' p

  infixr ` ◾* `:80 := pcompose2

  definition phomotopy_pinv_of_phomotopy_pid {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : g ∘* f ~* pid A) : f ~* g⁻¹ᵉ* :=
  phomotopy_pinv_left_of_phomotopy p ⬝* !pcompose_pid

  definition phomotopy_pinv_of_phomotopy_pid' {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : f ∘* g ~* pid B) : f ~* g⁻¹ᵉ* :=
  phomotopy_pinv_right_of_phomotopy p ⬝* !pid_pcompose

  definition pinv_phomotopy_of_pid_phomotopy {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : pid A ~* g ∘* f) : g⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid p⁻¹*)⁻¹*

  definition pinv_phomotopy_of_pid_phomotopy' {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : pid B ~* f ∘* g) : g⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid' p⁻¹*)⁻¹*

  definition pinv_pinv {A B : Type*} (f : A ≃* B) : (f⁻¹ᵉ*)⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid (pleft_inv f))⁻¹*

  definition pinv2 {A B : Type*} {f f' : A ≃* B} (p : f ~* f') : f⁻¹ᵉ* ~* f'⁻¹ᵉ* :=
  phomotopy_pinv_of_phomotopy_pid (pinv_right_phomotopy_of_phomotopy (!pid_pcompose ⬝* p)⁻¹*)

  postfix [parsing_only] `⁻²*`:(max+10) := pinv2

  definition trans_pinv {A B C : Type*} (f : A ≃* B) (g : B ≃* C) :
    (f ⬝e* g)⁻¹ᵉ* ~* f⁻¹ᵉ* ∘* g⁻¹ᵉ* :=
  begin
    refine (phomotopy_pinv_of_phomotopy_pid _)⁻¹*,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (!passoc⁻¹* ⬝* pwhisker_right _ !pright_inv ⬝* !pid_pcompose) ⬝* _,
    apply pright_inv
  end

  definition pinv_trans_pinv_left {A B C : Type*} (f : B ≃* A) (g : B ≃* C) :
    (f⁻¹ᵉ* ⬝e* g)⁻¹ᵉ* ~* f ∘* g⁻¹ᵉ* :=
  !trans_pinv ⬝* pwhisker_right _ !pinv_pinv

  definition pinv_trans_pinv_right {A B C : Type*} (f : A ≃* B) (g : C ≃* B) :
    (f ⬝e* g⁻¹ᵉ*)⁻¹ᵉ* ~* f⁻¹ᵉ* ∘* g :=
  !trans_pinv ⬝* pwhisker_left _ !pinv_pinv

  definition pinv_trans_pinv_pinv {A B C : Type*} (f : B ≃* A) (g : C ≃* B) :
    (f⁻¹ᵉ* ⬝e* g⁻¹ᵉ*)⁻¹ᵉ* ~* f ∘* g :=
  !trans_pinv ⬝* !pinv_pinv ◾* !pinv_pinv

  definition pinv_pcompose_cancel_left {A B C : Type*} (g : B ≃* C) (f : A →* B) :
    g⁻¹ᵉ* ∘* (g ∘* f) ~* f :=
  !passoc⁻¹* ⬝* pwhisker_right f !pleft_inv ⬝* !pid_pcompose

  definition pcompose_pinv_cancel_left {A B C : Type*} (g : C ≃* B) (f : A →* B) :
    g ∘* (g⁻¹ᵉ* ∘* f) ~* f :=
  !passoc⁻¹* ⬝* pwhisker_right f !pright_inv ⬝* !pid_pcompose

  definition pinv_pcompose_cancel_right {A B C : Type*} (g : B →* C) (f : B ≃* A) :
    (g ∘* f⁻¹ᵉ*) ∘* f ~* g :=
  !passoc ⬝* pwhisker_left g !pleft_inv ⬝* !pcompose_pid

  definition pcompose_pinv_cancel_right {A B C : Type*} (g : B →* C) (f : A ≃* B) :
    (g ∘* f) ∘* f⁻¹ᵉ* ~* g :=
  !passoc ⬝* pwhisker_left g !pright_inv ⬝* !pcompose_pid

  /- pointed equivalences between particular pointed types -/

  definition loopn_pequiv_loopn [constructor] (n : ℕ) (f : A ≃* B) : Ω[n] A ≃* Ω[n] B :=
  pequiv.MK2 (apn n f) (apn n f⁻¹ᵉ*)
  abstract begin
    induction n with n IH,
    { apply pleft_inv},
    { replace nat.succ n with n + 1,
      rewrite [+apn_succ],
      refine !ap1_pcompose⁻¹* ⬝* _,
      refine ap1_phomotopy IH ⬝* _,
      apply ap1_pid}
  end end
  abstract begin
    induction n with n IH,
    { apply pright_inv},
    { replace nat.succ n with n + 1,
      rewrite [+apn_succ],
      refine !ap1_pcompose⁻¹* ⬝* _,
      refine ap1_phomotopy IH ⬝* _,
      apply ap1_pid}
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

  definition loop_pequiv_loop_con {A B : Type*} (f : A ≃* B) (p q : Ω A)
    : loop_pequiv_loop f (p ⬝ q) = loop_pequiv_loop f p ⬝ loop_pequiv_loop f q :=
  loopn_pequiv_loopn_con 0 f p q

  definition loopn_pequiv_loopn_rfl (n : ℕ) (A : Type*) :
    loopn_pequiv_loopn n (pequiv.refl A) ~* pequiv.refl (Ω[n] A) :=
  begin
    exact !to_pmap_loopn_pequiv_loopn ⬝* apn_pid n,
  end

  definition loop_pequiv_loop_rfl (A : Type*) :
    loop_pequiv_loop (pequiv.refl A) ~* pequiv.refl (Ω A) :=
  loopn_pequiv_loopn_rfl 1 A

  definition pmap_functor [constructor] {A A' B B' : Type*} (f : A' →* A) (g : B →* B') :
    ppmap A B →* ppmap A' B' :=
  pmap.mk (λh, g ∘* h ∘* f)
    abstract begin
      fapply pmap_eq,
      { esimp, intro a, exact respect_pt g},
      { rewrite [▸*, ap_constant], apply idp_con}
    end end

  definition pequiv_pinverse (A : Type*) : Ω A ≃* Ω A :=
  pequiv_of_pmap pinverse !is_equiv_eq_inverse

  definition pequiv_of_eq_pt [constructor] {A : Type} {a a' : A} (p : a = a') :
    pointed.MK A a ≃* pointed.MK A a' :=
  pequiv_of_pmap (pmap_of_eq_pt p) !is_equiv_id

  definition pointed_eta_pequiv [constructor] (A : Type*) : A ≃* pointed.MK A pt :=
  pequiv.mk id !is_equiv_id idp

  /- every pointed map is homotopic to one of the form `pmap_of_map _ _`, up to some
     pointed equivalences -/
  definition phomotopy_pmap_of_map {A B : Type*} (f : A →* B) :
    (pointed_eta_pequiv B ⬝e* (pequiv_of_eq_pt (respect_pt f))⁻¹ᵉ*) ∘* f ∘*
      (pointed_eta_pequiv A)⁻¹ᵉ* ~* pmap_of_map f pt :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { esimp [pequiv.trans, pequiv.symm],
      exact !con.right_inv⁻¹ ⬝ ((!idp_con⁻¹ ⬝ !ap_id⁻¹) ◾ (!ap_id⁻¹⁻² ⬝ !idp_con⁻¹)), }
  end

/- -- TODO
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

  /- properties of iterated loop space -/
  variable (A)
  definition loopn_succ_in (n : ℕ) : Ω[succ n] A ≃* Ω[n] (Ω A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact loop_pequiv_loop IH}
  end

  definition loopn_add (n m : ℕ) : Ω[n] (Ω[m] A) ≃* Ω[m+n] (A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact loop_pequiv_loop IH}
  end

  definition loopn_succ_out (n : ℕ) : Ω[succ n] A ≃* Ω(Ω[n] A)  :=
  by reflexivity

  variable {A}

  theorem loopn_succ_in_con {n : ℕ} (p q : Ω[succ (succ n)] A) :
    loopn_succ_in A (succ n) (p ⬝ q) =
    loopn_succ_in A (succ n) p ⬝ loopn_succ_in A (succ n) q :=
  !loop_pequiv_loop_con

  definition loopn_loop_irrel (p : point A = point A) : Ω(pointed.Mk p) = Ω[2] A :=
  begin
    intros, fapply pType_eq,
    { esimp, transitivity _,
      apply eq_equiv_fn_eq_of_equiv (equiv_eq_closed_right _ p⁻¹),
      esimp, apply eq_equiv_eq_closed, apply con.right_inv, apply con.right_inv},
    { esimp, apply con.left_inv}
  end

  definition loopn_space_loop_irrel (n : ℕ) (p : point A = point A)
    : Ω[succ n](pointed.Mk p) = Ω[succ (succ n)] A :> pType :=
  calc
    Ω[succ n](pointed.Mk p) = Ω[n](Ω (pointed.Mk p)) : eq_of_pequiv !loopn_succ_in
      ... = Ω[n] (Ω[2] A)                            : loopn_loop_irrel
      ... = Ω[2+n] A                                 : eq_of_pequiv !loopn_add
      ... = Ω[n+2] A                                 : by rewrite [algebra.add.comm]

  definition apn_succ_phomotopy_in (n : ℕ) (f : A →* B) :
    loopn_succ_in B n ∘* Ω→[n + 1] f ~* Ω→[n] (Ω→ f) ∘* loopn_succ_in A n :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact !ap1_pcompose⁻¹* ⬝* ap1_phomotopy IH ⬝* !ap1_pcompose}
  end

  definition loopn_succ_in_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    loopn_succ_in B n ∘* Ω→[n+1] f ~* Ω→[n] (Ω→ f) ∘* loopn_succ_in A n :=
  !apn_succ_phomotopy_in

  definition loopn_succ_in_inv_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    Ω→[n + 1] f ∘* (loopn_succ_in A n)⁻¹ᵉ* ~* (loopn_succ_in B n)⁻¹ᵉ* ∘* Ω→[n] (Ω→ f):=
  begin
    apply pinv_right_phomotopy_of_phomotopy,
    refine _ ⬝* !passoc⁻¹*,
    apply phomotopy_pinv_left_of_phomotopy,
    apply apn_succ_phomotopy_in
  end

  /- properties of ppmap, the pointed type of pointed maps -/
  definition ppcompose_left [constructor] (g : B →* C) : ppmap A B →* ppmap A C :=
  pmap.mk (pcompose g) (eq_of_phomotopy (phomotopy.mk (λa, respect_pt g) (idp_con _)⁻¹))

  definition is_pequiv_ppcompose_left [instance] [constructor] (g : B →* C) [H : is_equiv g] :
    is_equiv (@ppcompose_left A B C g) :=
  begin
    fapply is_equiv.adjointify,
    { exact (ppcompose_left (pequiv_of_pmap g H)⁻¹ᵉ*) },
    all_goals (intros f; esimp; apply eq_of_phomotopy),
    { exact calc g ∘* ((pequiv_of_pmap g H)⁻¹ᵉ* ∘* f)
              ~* (g ∘* (pequiv_of_pmap g H)⁻¹ᵉ*) ∘* f : passoc
          ... ~* pid _ ∘* f : pwhisker_right f (pright_inv (pequiv_of_pmap g H))
          ... ~* f : pid_pcompose f },
    { exact calc (pequiv_of_pmap g H)⁻¹ᵉ* ∘* (g ∘* f)
              ~* ((pequiv_of_pmap g H)⁻¹ᵉ* ∘* g) ∘* f : passoc
          ... ~* pid _ ∘* f : pwhisker_right f (pleft_inv (pequiv_of_pmap g H))
          ... ~* f : pid_pcompose f }
  end

  definition pequiv_ppcompose_left [constructor] (g : B ≃* C) : ppmap A B ≃* ppmap A C :=
  pequiv_of_pmap (ppcompose_left g) _

  definition pcompose_pconst [constructor] (f : B →* C) : f ∘* pconst A B ~* pconst A C :=
  phomotopy.mk (λa, respect_pt f) (idp_con _)⁻¹

  definition pconst_pcompose [constructor] (f : A →* B) : pconst B C ∘* f ~* pconst A C :=
  phomotopy.mk (λa, rfl) (ap_constant _ _)⁻¹

  definition ppcompose_right [constructor] (f : A →* B) : ppmap B C →* ppmap A C :=
  begin
    fconstructor,
    { intro g, exact g ∘* f },
    { apply eq_of_phomotopy, esimp, apply pconst_pcompose }
  end

  definition pequiv_ppcompose_right [constructor] (f : A ≃* B) : ppmap B C ≃* ppmap A C :=
  begin
    fapply pequiv.MK,
    { exact ppcompose_right f },
    { exact ppcompose_right f⁻¹ᵉ* },
    { intro g, apply eq_of_phomotopy, refine !passoc ⬝* _,
      refine pwhisker_left g !pright_inv ⬝* !pcompose_pid, },
    { intro g, apply eq_of_phomotopy, refine !passoc ⬝* _,
      refine pwhisker_left g !pleft_inv ⬝* !pcompose_pid, },
  end

  definition loop_pmap_commute (A B : Type*) : Ω(ppmap A B) ≃* (ppmap A (Ω B)) :=
    pequiv_of_equiv
      (calc Ω(ppmap A B) ≃ (pconst A B ~* pconst A B)                       : pmap_eq_equiv _ _
                     ... ≃ Σ(p : pconst A B ~ pconst A B), p pt ⬝ rfl = rfl : phomotopy.sigma_char
                     ... ≃ (A →* Ω B)                                       : pmap.sigma_char)
      (by reflexivity)

  definition papply [constructor] {A : Type*} (B : Type*) (a : A) : ppmap A B →* B :=
  pmap.mk (λ(f : A →* B), f a) idp

  definition papply_pcompose [constructor] {A : Type*} (B : Type*) (a : A) : ppmap A B →* B :=
  pmap.mk (λ(f : A →* B), f a) idp

  definition pmap_pbool_pequiv [constructor] (B : Type*) : ppmap pbool B ≃* B :=
  begin
    fapply pequiv.MK,
    { exact papply B tt },
    { exact pbool_pmap },
    { intro f, fapply pmap_eq,
      { intro b, cases b, exact !respect_pt⁻¹, reflexivity },
      { exact !con.left_inv⁻¹ }},
    { intro b, reflexivity },
  end

  definition papn_pt [constructor] (n : ℕ) (A B : Type*) : ppmap A B →* ppmap (Ω[n] A) (Ω[n] B) :=
  pmap.mk (λf, apn n f) (eq_of_phomotopy !apn_pconst)

  definition papn_fun [constructor] {n : ℕ} {A : Type*} (B : Type*) (p : Ω[n] A) :
    ppmap A B →* Ω[n] B :=
  papply _ p ∘* papn_pt n A B


end pointed
