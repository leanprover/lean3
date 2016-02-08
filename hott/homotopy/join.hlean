/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Ulrik Buchholtz

Declaration of a join as a special case of a pushout
-/

import hit.pushout .sphere cubical.cube

open eq function prod equiv is_trunc bool sigma.ops

definition join (A B : Type) : Type := @pushout.pushout (A × B) A B pr1 pr2

namespace join
  section
  variables {A B : Type}

  definition inl (a : A) : join A B := @pushout.inl (A × B) A B pr1 pr2 a
  definition inr (b : B) : join A B := @pushout.inr (A × B) A B pr1 pr2 b

  definition glue (a : A) (b : B) : inl a = inr b :=
  @pushout.glue (A × B) A B pr1 pr2 (a, b)

  protected definition rec {P : join A B → Type}
    (Pinl : Π(x : A), P (inl x))
    (Pinr : Π(y : B), P (inr y))
    (Pglue : Π(x : A)(y : B), Pinl x =[glue x y] Pinr y)
    (z : join A B) : P z :=
  pushout.rec Pinl Pinr (prod.rec Pglue) z

  protected definition rec_glue {P : join A B → Type}
    (Pinl : Π(x : A), P (inl x))
    (Pinr : Π(y : B), P (inr y))
    (Pglue : Π(x : A)(y : B), Pinl x =[glue x y] Pinr y)
    (x : A) (y : B)
    : apdo (join.rec Pinl Pinr Pglue) (glue x y) = Pglue x y :=
  !quotient.rec_eq_of_rel

  protected definition elim {P : Type} (Pinl : A → P) (Pinr : B → P)
    (Pglue : Π(x : A)(y : B), Pinl x = Pinr y) (z : join A B) : P :=
  join.rec Pinl Pinr (λx y, pathover_of_eq (Pglue x y)) z

  protected definition elim_glue {P : Type} (Pinl : A → P) (Pinr : B → P)
    (Pglue : Π(x : A)(y : B), Pinl x = Pinr y) (x : A) (y : B)
    : ap (join.elim Pinl Pinr Pglue) (glue x y) = Pglue x y :=
  begin
    apply equiv.eq_of_fn_eq_fn_inv !(pathover_constant (glue x y)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑join.elim],
    apply join.rec_glue
  end

  protected definition elim_ap_inl {P : Type} (Pinl : A → P) (Pinr : B → P)
    (Pglue : Π(x : A)(y : B), Pinl x = Pinr y) {a a' : A} (p : a = a')
    : ap (join.elim Pinl Pinr Pglue) (ap inl p) = ap Pinl p :=
  by cases p; reflexivity

  protected definition hsquare {a a' : A} {b b' : B} (p : a = a') (q : b = b') :
    square (ap inl p) (ap inr q) (glue a b) (glue a' b') :=
  eq.rec_on p (eq.rec_on q hrfl)

  protected definition vsquare {a a' : A} {b b' : B} (p : a = a') (q : b = b') :
    square (glue a b) (glue a' b') (ap inl p) (ap inr q) :=
  eq.rec_on p (eq.rec_on q vrfl)

end

end join

attribute join.inl join.inr [constructor]
attribute join.rec [recursor]
attribute join.elim [recursor 7]
attribute join.rec join.elim [unfold 7]

/- Diamonds in joins -/
namespace join
  variables {A B : Type}

  protected definition diamond (a a' : A) (b b' : B) :=
  square (glue a b) (glue a' b')⁻¹ (glue a b') (glue a' b)⁻¹

  protected definition hdiamond {a a' : A} (b b' : B) (p : a = a')
    : join.diamond a a' b b' :=
  begin
    cases p, unfold join.diamond,
    assert H : (glue a b' ⬝ (glue a b')⁻¹ ⬝ (glue a b)⁻¹⁻¹) = glue a b,
    { rewrite [con.right_inv,inv_inv,idp_con] },
    exact H ▸ top_deg_square (glue a b') (glue a b')⁻¹ (glue a b)⁻¹,
  end

  protected definition vdiamond (a a' : A) {b b' : B} (q : b = b')
    : join.diamond a a' b b' :=
  begin
    cases q, unfold join.diamond,
    assert H : (glue a b ⬝ (glue a' b)⁻¹ ⬝ (glue a' b)⁻¹⁻¹) = glue a b,
    { rewrite [con.assoc,con.right_inv] },
    exact H ▸ top_deg_square (glue a b) (glue a' b)⁻¹ (glue a' b)⁻¹
  end

  protected definition symm_diamond (a : A) (b : B)
    : join.vdiamond a a idp = join.hdiamond b b idp :=
  begin
    unfold join.hdiamond, unfold join.vdiamond,
    assert H : Π{X : Type} ⦃x y : X⦄ (p : x = y),
      eq.rec (eq.rec (refl p) (symm (con.right_inv p⁻¹)))
             (symm (con.assoc p p⁻¹ p⁻¹⁻¹)) ▸ top_deg_square p p⁻¹ p⁻¹
    = eq.rec (eq.rec (eq.rec (refl p) (symm (idp_con p))) (symm (inv_inv p)))
             (symm (con.right_inv p)) ▸ top_deg_square p p⁻¹ p⁻¹
      :> square p p⁻¹ p p⁻¹,
    { intros X x y p, cases p, reflexivity },
   apply H (glue a b)
  end

end join

namespace join

  variables {A₁ A₂ B₁ B₂ : Type}
  protected definition functor [reducible]
    (f : A₁ → A₂) (g : B₁ → B₂) : join A₁ B₁ → join A₂ B₂ :=
  begin
    intro x, induction x with a b a b,
    { exact inl (f a) }, { exact inr (g b) }, { apply glue }
  end

  protected definition ap_diamond (f : A₁ → A₂) (g : B₁ → B₂)
    {a a' : A₁} {b b' : B₁}
    : join.diamond a a' b b' → join.diamond (f a) (f a') (g b) (g b') :=
  begin
    unfold join.diamond, intro s,
    note s' := aps (join.functor f g) s,
    do 2 rewrite eq.ap_inv at s',
    do 4 rewrite join.elim_glue at s', exact s'
  end

  protected definition equiv_closed
    : A₁ ≃ A₂ → B₁ ≃ B₂ → join A₁ B₁ ≃ join A₂ B₂ :=
  begin
    intros H K,
    fapply equiv.MK,
    { intro x, induction x with a b a b,
      { exact inl (to_fun H a) }, { exact inr (to_fun K b) },
      { apply glue } },
    { intro y, induction y with a b a b,
      { exact inl (to_inv H a) }, { exact inr (to_inv K b) },
      { apply glue } },
    { intro y, induction y with a b a b,
      { apply ap inl, apply to_right_inv },
      { apply ap inr, apply to_right_inv },
      { apply eq_pathover, rewrite ap_id,
        rewrite (ap_compose' (join.elim _ _ _)),
        do 2 krewrite join.elim_glue, apply join.hsquare } },
    { intro x, induction x with a b a b,
      { apply ap inl, apply to_left_inv },
      { apply ap inr, apply to_left_inv },
      { apply eq_pathover, rewrite ap_id,
        rewrite (ap_compose' (join.elim _ _ _)),
        do 2 krewrite join.elim_glue, apply join.hsquare } }
  end

  protected definition twist_diamond {A : Type} {a a' : A} (p : a = a')
    : pathover (λx, join.diamond a' x a x)
        (join.vdiamond a' a idp) p
        (join.hdiamond a a' idp) :=
  begin
    cases p, apply pathover_idp_of_eq, apply join.symm_diamond
  end

  protected definition empty (A : Type) : join empty A ≃ A :=
  begin
    fapply equiv.MK,
    { intro x, induction x with z a z a,
      { induction z },
      { exact a },
      { induction z } },
    { intro a, exact inr a },
    { intro a, reflexivity },
    { intro x, induction x with z a z a,
      { induction z },
      { reflexivity },
      { induction z } }
  end

  protected definition bool (A : Type) : join bool A ≃ susp A :=
  begin
    fapply equiv.MK,
    { intro ba, induction ba with [b, a, b, a],
      { induction b, exact susp.south, exact susp.north },
      { exact susp.north },
      { induction b, esimp,
        { apply inverse, apply susp.merid, exact a },
        { reflexivity } } },
    { intro s, induction s with a,
      { exact inl tt },
      { exact inl ff },
      { exact (glue tt a) ⬝ (glue ff a)⁻¹ } },
    { intro s, induction s with a,
      { reflexivity },
      { reflexivity },
      { esimp, apply eq_pathover, rewrite ap_id,
        rewrite (ap_compose' (join.elim _ _ _)),
        rewrite [susp.elim_merid,ap_con,ap_inv],
        krewrite [join.elim_glue,join.elim_glue],
        esimp, rewrite [inv_inv,idp_con],
        apply hdeg_square, reflexivity } },
    { intro ba, induction ba with [b, a, b, a], esimp,
      { induction b, do 2 reflexivity },
      { apply glue },
      { induction b,
        { esimp, apply eq_pathover, rewrite ap_id,
          rewrite (ap_compose' (susp.elim _ _ _)),
          krewrite join.elim_glue, rewrite ap_inv,
          krewrite susp.elim_merid,
          apply square_of_eq_top, apply inverse,
          rewrite con.assoc, apply con.left_inv },
        { esimp, apply eq_pathover, rewrite ap_id,
          rewrite (ap_compose' (susp.elim _ _ _)),
          krewrite join.elim_glue, esimp,
          apply square_of_eq_top,
          rewrite [idp_con,con.right_inv] } } }
  end

end join

namespace join
  variables (A B C : Type)

  protected definition is_contr [HA : is_contr A] :
    is_contr (join A B) :=
  begin
    fapply is_contr.mk, exact inl (center A),
    intro x, induction x with a b a b, apply ap inl, apply center_eq,
    apply glue, apply pathover_of_tr_eq,
    apply concat, apply transport_eq_Fr, esimp, rewrite ap_id,
    generalize center_eq a, intro p, cases p, apply idp_con,
  end

  protected definition swap : join A B → join B A :=
  begin
    intro x, induction x with a b a b, exact inr a, exact inl b,
    apply !glue⁻¹
  end

  protected definition swap_involutive (x : join A B) :
    join.swap B A (join.swap A B x) = x :=
  begin
    induction x with a b a b, do 2 reflexivity,
    apply eq_pathover, rewrite ap_id,
    apply hdeg_square, esimp[join.swap],
    apply concat, apply ap_compose' (join.elim _ _ _),
    krewrite [join.elim_glue, ap_inv, join.elim_glue], apply inv_inv,
  end

  protected definition symm : join A B ≃ join B A :=
  by fapply equiv.MK; do 2 apply join.swap; do 2 apply join.swap_involutive

end join

/- This proves that the join operator is associative.
   The proof is more or less ported from Evan Cavallo's agda version:
   https://github.com/HoTT/HoTT-Agda/blob/master/homotopy/JoinAssocCubical.agda -/
namespace join

section join_switch

  private definition massage_sq' {A : Type} {a₀₀ a₂₀ a₀₂ a₂₂ : A}
    {p₁₀ : a₀₀ = a₂₀} {p₁₂ :  a₀₂ = a₂₂} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂}
    (sq : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀⁻¹ p₀₁⁻¹ (p₂₁ ⬝ p₁₂⁻¹) idp :=
  by induction sq; exact ids

  private definition massage_sq {A : Type} {a₀₀ a₂₀ a₀₂ : A}
    {p₁₀ : a₀₀ = a₂₀} {p₁₂ :  a₀₂ = a₂₀} {p₀₁ : a₀₀ = a₀₂}
    (sq : square p₁₀ p₁₂ p₀₁ idp) : square p₁₀⁻¹ p₀₁⁻¹ p₁₂⁻¹ idp :=
  !idp_con⁻¹ ⬝ph (massage_sq' sq)

  private definition ap_square_massage {A B : Type} (f : A → B) {a₀₀ a₀₂ a₂₀ : A}
    {p₀₁ : a₀₀ = a₀₂} {p₁₀ : a₀₀ = a₂₀} {p₁₁ : a₂₀ = a₀₂} (sq : square p₀₁ p₁₁ p₁₀ idp) :
    cube (hdeg_square (ap_inv f p₁₁)) ids
         (aps f (massage_sq sq)) (massage_sq (aps f sq))
         (hdeg_square !ap_inv) (hdeg_square !ap_inv) :=
  by apply rec_on_r sq; apply idc

  private definition massage_cube' {A : Type} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ : A}
    {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂} {p₁₂₀ : a₀₂₀ = a₂₂₀}
    {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂} {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂}
    {p₀₂₁ : a₀₂₀ = a₀₂₂} {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
    {s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} {s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
    {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁} {s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
    {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁} {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
    cube (s₂₁₁ ⬝v s₁₁₂⁻¹ᵛ) vrfl (massage_sq' s₁₀₁) (massage_sq' s₁₂₁) s₁₁₀⁻¹ᵛ s₀₁₁⁻¹ᵛ :=
  by cases c; apply idc

  private definition massage_cube {A : Type} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₀₂₂ : A}
    {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂} {p₁₂₀ : a₀₂₀ = a₂₂₀}
    {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₁₀₂ : a₀₀₂ = a₂₀₀} {p₀₁₂ : a₀₀₂ = a₀₂₂}
    {p₀₂₁ : a₀₂₀ = a₀₂₂} {p₁₂₂ : a₀₂₂ = a₂₂₀}
    {s₁₁₀ : square p₀₁₀ _ _ _} {s₁₁₂ : square p₀₁₂ p₂₁₀ p₁₀₂ p₁₂₂}
    {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁} --{s₂₁₁ : square p₂₁₀ p₂₁₀ idp idp}
    {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ idp} {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ idp}
    (c : cube s₀₁₁ vrfl s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
    cube s₁₁₂⁻¹ᵛ vrfl (massage_sq s₁₀₁) (massage_sq s₁₂₁) s₁₁₀⁻¹ᵛ s₀₁₁⁻¹ᵛ :=
  begin
    cases p₁₀₀, cases p₁₀₂, cases p₁₂₂, note c' := massage_cube' c, esimp[massage_sq],
    krewrite vdeg_v_eq_ph_pv_hp at c', exact c',
  end

  private definition massage_massage {A : Type} {a₀₀ a₀₂ a₂₀ : A}
    {p₀₁ : a₀₀ = a₀₂} {p₁₀ : a₀₀ = a₂₀} {p₁₁ : a₂₀  = a₀₂} (sq : square p₀₁ p₁₁ p₁₀ idp) :
    cube (hdeg_square !inv_inv) ids (massage_sq (massage_sq sq))
      sq (hdeg_square !inv_inv) (hdeg_square !inv_inv) :=
  by apply rec_on_r sq; apply idc

  private definition square_Flr_ap_idp_cube {A B : Type} {b : B} {f : A → B}
    {p₁ p₂ : Π a, f a = b} (α : Π a, p₁ a = p₂ a) {a₁ a₂ : A} (q : a₁ = a₂) :
    cube hrfl hrfl (square_Flr_ap_idp p₁ q) (square_Flr_ap_idp p₂ q)
      (hdeg_square (α _)) (hdeg_square (α _)) :=
  by cases q; esimp[square_Flr_ap_idp]; apply deg3_cube; esimp

  variables {A B C : Type}

  definition switch_left [reducible] : join A B → join (join C B) A :=
  begin
    intro x, induction x with a b a b, exact inr a, exact inl (inr b), apply !glue⁻¹,
  end

  private definition switch_coh_fill_square (a : A) (b : B) (c : C) :=
  square (glue (inl c) a)⁻¹ (ap inl (glue c b))⁻¹ (ap switch_left (glue a b)) idp

  private definition switch_coh_fill_cube (a : A) (b : B) (c : C)
    (sq : switch_coh_fill_square a b c) :=
  cube (hdeg_square !join.elim_glue) ids
       sq (massage_sq !square_Flr_ap_idp)
       hrfl hrfl

  private definition switch_coh_fill_type (a : A) (b : B) (c : C) :=
  Σ sq : switch_coh_fill_square a b c, switch_coh_fill_cube a b c sq

  private definition switch_coh_fill (a : A) (b : B) (c : C)
    : switch_coh_fill_type a b c :=
  by esimp; apply cube_fill101

  private definition switch_coh (ab : join A B) (c : C) : switch_left ab = inl (inl c) :=
  begin
    induction ab with a b a b, apply !glue⁻¹, apply (ap inl !glue)⁻¹,
    apply eq_pathover, refine _ ⬝hp !ap_constant⁻¹,
    apply !switch_coh_fill.1,
  end

  protected definition switch [reducible] : join (join A B) C → join (join C B) A :=
  begin
    intro x, induction x with ab c ab c, exact switch_left ab, exact inl (inl c),
    exact switch_coh ab c,
  end

  private definition switch_inv_left_square (a : A) (b : B) :
    square idp idp (ap (!(@join.switch C) ∘ switch_left) (glue a b)) (ap inl (glue a b)) :=
  begin
    refine hdeg_square !ap_compose ⬝h _,
    refine aps join.switch (hdeg_square !join.elim_glue) ⬝h _, esimp,
    refine hdeg_square !(ap_inv join.switch) ⬝h _,
    refine hrfl⁻¹ʰ⁻¹ᵛ ⬝h _, esimp[join.switch,switch_left,switch_coh],
    refine (hdeg_square !join.elim_glue)⁻¹ᵛ ⬝h _, esimp,
    refine hrfl⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private definition switch_inv_coh_left (c : C) (a : A) :
    square idp idp (ap !(@join.switch C B) (switch_coh (inl a) c)) (glue (inl a) c) :=
  begin
    refine hrfl ⬝h _,
    refine aps join.switch hrfl ⬝h _, esimp[switch_coh],
    refine hdeg_square !ap_inv ⬝h _,
    refine hrfl⁻¹ʰ⁻¹ᵛ ⬝h _, esimp[join.switch,switch_left],
    refine (hdeg_square !join.elim_glue)⁻¹ᵛ ⬝h _,
    refine hrfl⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private definition switch_inv_coh_right (c : C) (b : B) :
    square idp idp (ap !(@join.switch _ _ A) (switch_coh (inr b) c)) (glue (inr b) c) :=
  begin
    refine hrfl ⬝h _,
    refine aps join.switch hrfl ⬝h _, esimp[switch_coh],
    refine hdeg_square !ap_inv ⬝h _,
    refine (hdeg_square !ap_compose)⁻¹ʰ⁻¹ᵛ ⬝h _,
    refine hrfl⁻¹ᵛ ⬝h _, esimp[join.switch,switch_left],
    refine (hdeg_square !join.elim_glue)⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private definition switch_inv_left (ab : join A B) :
    !(@join.switch C) (join.switch (inl ab)) = inl ab :=
  begin
    induction ab with a b a b, do 2 reflexivity,
    apply eq_pathover, exact !switch_inv_left_square,
  end

  section
    variables (a : A) (b : B) (c : C)

    private definition switch_inv_cube_aux1 {A B C : Type} {b : B} {f : A → B} (h : B → C)
      (g : Π a, f a = b) {x y : A} (p : x = y) :
      cube (hdeg_square (ap_compose h f p)) ids (square_Flr_ap_idp (λ a, ap h (g a)) p)
      (aps h (square_Flr_ap_idp _ _)) hrfl hrfl :=
    by cases p; esimp[square_Flr_ap_idp]; apply deg2_cube; cases (g x); esimp

    private definition switch_inv_cube_aux2 {A B : Type} {b : B} {f : A → B}
      (g : Π a, f a = b) {x y : A} (p : x = y) {sq : square (g x) (g y) (ap f p) idp}
      (q : apdo g p = eq_pathover (sq ⬝hp !ap_constant⁻¹)) : square_Flr_ap_idp _ _ = sq :=
    begin
      cases p, esimp at *, apply concat, apply inverse, apply vdeg_square_idp,
      apply concat, apply ap vdeg_square, exact ap eq_of_pathover_idp q,
      krewrite (is_equiv.right_inv (equiv.to_fun !pathover_idp)),
      exact is_equiv.left_inv (equiv.to_fun (vdeg_square_equiv _ _)) sq,
    end

    private definition switch_inv_cube (a : A) (b : B) (c : C) :
      cube (switch_inv_left_square a b) ids (square_Flr_ap_idp _ _)
      (square_Flr_ap_idp _ _) (switch_inv_coh_left c a) (switch_inv_coh_right c b) :=
    begin
      esimp [switch_inv_coh_left, switch_inv_coh_right, switch_inv_left_square],
      apply cube_concat2, apply switch_inv_cube_aux1,
      apply cube_concat2, apply cube_transport101, apply inverse,
        apply ap (λ x, aps join.switch x), apply switch_inv_cube_aux2, apply join.rec_glue,
        apply apc, apply (switch_coh_fill a b c).2,
      apply cube_concat2, esimp, apply ap_square_massage,
      apply cube_concat2, apply massage_cube, apply cube_inverse2, apply switch_inv_cube_aux1,
      apply cube_concat2, apply massage_cube, apply square_Flr_ap_idp_cube,
      apply cube_concat2, apply massage_cube, apply cube_transport101,
        apply inverse, apply switch_inv_cube_aux2,
        esimp[switch_coh], apply join.rec_glue, apply (switch_coh_fill c b a).2,
      apply massage_massage,
    end

  end

  private definition pathover_of_triangle_cube {A B : Type} {b₀ b₁ : A → B}
    {b : B} {p₀₁ : Π a, b₀ a = b₁ a} {p₀ : Π a, b₀ a = b} {p₁ : Π a, b₁ a = b}
    {x y : A} {q : x = y} {sqx : square (p₀₁ x) idp (p₀ x) (p₁ x)}
    {sqy : square (p₀₁ y) idp (p₀ y) (p₁ y)}
    (c : cube (natural_square_tr _ _) ids (square_Flr_ap_idp p₀ q) (square_Flr_ap_idp p₁ q)
       sqx sqy) :
    sqx =[q] sqy :=
  by cases q; apply pathover_of_eq_tr; apply eq_of_deg12_cube; exact c

  private definition pathover_of_ap_ap_square {A : Type} {x y : A} {p : x = y}
    (g : B → A) (f : A → B) {u : g (f x) = x} {v : g (f y) = y}
    (sq : square (ap g (ap f p)) p u v) : u =[p] v :=
  by cases p; apply eq_pathover; apply transpose; exact sq

  private definition natural_square_tr_beta {A B : Type} {f₁ f₂ : A → B}
    (p : Π a, f₁ a = f₂ a) {x y : A} (q : x = y) {sq : square (p x) (p y) (ap f₁ q) (ap f₂ q)}
    (e : apdo p q = eq_pathover sq) :
    natural_square_tr p q = sq :=
  begin
    cases q, esimp at *, apply concat, apply inverse, apply vdeg_square_idp,
    apply concat, apply ap vdeg_square, apply ap eq_of_pathover_idp e,
    krewrite (is_equiv.right_inv (equiv.to_fun !pathover_idp)),
    exact is_equiv.left_inv (equiv.to_fun (vdeg_square_equiv _ _)) sq,
  end

  private definition switch_inv_coh (c : C) (k : join A B) :
    square (switch_inv_left k) idp (ap join.switch (switch_coh k c)) (glue k c) :=
  begin
    induction k with a b a b, apply switch_inv_coh_left, apply switch_inv_coh_right,
    refine pathover_of_triangle_cube _,
    esimp, apply cube_transport011,
    apply inverse, rotate 1, apply switch_inv_cube,
    apply natural_square_tr_beta, apply join.rec_glue,
  end

  protected definition switch_involutive (x : join (join A B) C) :
    join.switch (join.switch x) = x :=
  begin
    induction x with ab c ab c, apply switch_inv_left, reflexivity,
    apply pathover_of_ap_ap_square join.switch join.switch,
    krewrite join.elim_glue, esimp,
    apply transpose, exact !switch_inv_coh,
  end

end join_switch

  protected definition switch_equiv (A B C : Type) : join (join A B) C ≃ join (join C B) A :=
  by apply equiv.MK; do 2 apply join.switch_involutive

  protected definition assoc (A B C : Type) : join (join A B) C ≃ join A (join B C) :=
  calc join (join A B) C ≃ join (join C B) A : join.switch_equiv
                     ... ≃ join A (join C B) : join.symm
                     ... ≃ join A (join B C) : join.equiv_closed erfl (join.symm C B)

  protected definition ap_assoc_inv_glue_inl {A B : Type} (C : Type) (a : A) (b : B)
    : ap (to_inv (join.assoc A B C)) (glue a (inl b)) = ap inl (glue a b) :=
  begin
    unfold join.assoc, unfold equiv.trans, rewrite ap_compose, krewrite join.elim_glue,
    rewrite ap_compose, krewrite join.elim_glue, rewrite ap_inv, krewrite join.elim_glue,
    unfold switch_coh, unfold join.symm, unfold join.swap, esimp, rewrite eq.inv_inv
  end

  protected definition ap_assoc_inv_glue_inr {A C : Type} (B : Type) (a : A) (c : C)
    : ap (to_inv (join.assoc A B C)) (glue a (inr c)) = glue (inl a) c :=
  begin
    unfold join.assoc, unfold equiv.trans, rewrite ap_compose, krewrite join.elim_glue,
    rewrite ap_compose, krewrite join.elim_glue, rewrite ap_inv, krewrite join.elim_glue,
    unfold switch_coh, unfold join.symm, unfold join.swap, esimp, rewrite eq.inv_inv
  end

end join

namespace join

  open sphere sphere_index sphere.ops
  protected definition spheres (n m : ℕ₋₁) : join (S n) (S m) ≃ S (n+1+m) :=
  begin
    apply equiv.trans (join.symm (S n) (S m)),
    induction m with m IH,
    { exact join.empty (S n) },
    { calc join (S m.+1) (S n)
           ≃ join (join bool (S m)) (S n)
           : join.equiv_closed (equiv.symm (join.bool (S m))) erfl
       ... ≃ join bool (join (S m) (S n))
           : join.assoc
       ... ≃ join bool (S (n+1+m))
           : join.equiv_closed erfl IH
       ... ≃ sphere (n+1+m.+1)
           : join.bool (S (n+1+m)) }
  end

end join
