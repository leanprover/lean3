/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Basic theorems about pathovers
-/

prelude
import .path .equiv

open equiv is_equiv function

variables {A A' : Type} {B B' : A → Type} {B'' : A' → Type} {C : Π⦃a⦄, B a → Type}
          {a a₂ a₃ a₄ : A} {p p' : a = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄} {p₁₃ : a = a₃}
          {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
          {c : C b} {c₂ : C b₂}

namespace eq
  inductive pathover.{l} (B : A → Type.{l}) (b : B a) : Π{a₂ : A}, a = a₂ → B a₂ → Type.{l} :=
  idpatho : pathover B b (refl a) b

  notation b ` =[`:50 p:0 `] `:0 b₂:50 := pathover _ b p b₂

  definition idpo [reducible] [constructor] : b =[refl a] b :=
  pathover.idpatho b

  /- equivalences with equality using transport -/
  definition pathover_of_tr_eq [unfold 5 8] (r : p ▸ b = b₂) : b =[p] b₂ :=
  by cases p; cases r; constructor

  definition pathover_of_eq_tr [unfold 5 8] (r : b = p⁻¹ ▸ b₂) : b =[p] b₂ :=
  by cases p; cases r; constructor

  definition tr_eq_of_pathover [unfold 8] (r : b =[p] b₂) : p ▸ b = b₂ :=
  by cases r; reflexivity

  definition eq_tr_of_pathover [unfold 8] (r : b =[p] b₂) : b = p⁻¹ ▸ b₂ :=
  by cases r; reflexivity

  definition pathover_equiv_tr_eq [constructor] (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) ≃ (p ▸ b = b₂) :=
  begin
    fapply equiv.MK,
    { exact tr_eq_of_pathover},
    { exact pathover_of_tr_eq},
    { intro r, cases p, cases r, apply idp},
    { intro r, cases r, apply idp},
  end

  definition pathover_equiv_eq_tr [constructor] (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) ≃ (b = p⁻¹ ▸ b₂) :=
  begin
    fapply equiv.MK,
    { exact eq_tr_of_pathover},
    { exact pathover_of_eq_tr},
    { intro r, cases p, cases r, apply idp},
    { intro r, cases r, apply idp},
  end

  definition pathover_tr [unfold 5] (p : a = a₂) (b : B a) : b =[p] p ▸ b :=
  by cases p; constructor

  definition tr_pathover [unfold 5] (p : a = a₂) (b : B a₂) : p⁻¹ ▸ b =[p] b :=
  by cases p; constructor

  definition concato [unfold 12] (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) : b =[p ⬝ p₂] b₃ :=
  by induction r₂; exact r

  definition inverseo [unfold 8] (r : b =[p] b₂) : b₂ =[p⁻¹] b :=
  by induction r; constructor

  definition concato_eq [unfold 10] (r : b =[p] b₂) (q : b₂ = b₂') : b =[p] b₂' :=
  by induction q; exact r

  definition eq_concato [unfold 9] (q : b = b') (r : b' =[p] b₂) : b =[p] b₂ :=
  by induction q; exact r

  definition change_path [unfold 9] (q : p = p') (r : b =[p] b₂) : b =[p'] b₂ :=
  q ▸ r

  -- infix ` ⬝ ` := concato
  infix ` ⬝o `:72 := concato
  infix ` ⬝op `:73 := concato_eq
  infix ` ⬝po `:73 := eq_concato
  -- postfix `⁻¹` := inverseo
  postfix `⁻¹ᵒ`:(max+10) := inverseo

  definition pathover_cancel_right (q : b =[p ⬝ p₂] b₃) (r : b₃ =[p₂⁻¹] b₂) : b =[p] b₂ :=
  change_path !con_inv_cancel_right (q ⬝o r)

  definition pathover_cancel_right' (q : b =[p₁₃ ⬝ p₂⁻¹] b₂) (r : b₂ =[p₂] b₃) : b =[p₁₃] b₃ :=
  change_path !inv_con_cancel_right (q ⬝o r)

  definition pathover_cancel_left (q : b₂ =[p⁻¹] b) (r : b =[p ⬝ p₂] b₃) : b₂ =[p₂] b₃ :=
  change_path !inv_con_cancel_left (q ⬝o r)

  definition pathover_cancel_left' (q : b =[p] b₂) (r : b₂ =[p⁻¹ ⬝ p₁₃] b₃) : b =[p₁₃] b₃ :=
  change_path !con_inv_cancel_left (q ⬝o r)

  /- Some of the theorems analogous to theorems for = in init.path -/

  definition cono_idpo (r : b =[p] b₂) : r ⬝o idpo =[con_idp p] r :=
  pathover.rec_on r idpo

  definition idpo_cono (r : b =[p] b₂) : idpo ⬝o r =[idp_con p] r :=
  pathover.rec_on r idpo

  definition cono.assoc' (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) (r₃ : b₃ =[p₃] b₄) :
    r ⬝o (r₂ ⬝o r₃) =[!con.assoc'] (r ⬝o r₂) ⬝o r₃ :=
  pathover.rec_on r₃ (pathover.rec_on r₂ (pathover.rec_on r idpo))

  definition cono.assoc (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) (r₃ : b₃ =[p₃] b₄) :
    (r ⬝o r₂) ⬝o r₃ =[!con.assoc] r ⬝o (r₂ ⬝o r₃) :=
  pathover.rec_on r₃ (pathover.rec_on r₂ (pathover.rec_on r idpo))

  definition cono.right_inv (r : b =[p] b₂) : r ⬝o r⁻¹ᵒ =[!con.right_inv] idpo :=
  pathover.rec_on r idpo

  definition cono.left_inv (r : b =[p] b₂) : r⁻¹ᵒ ⬝o r =[!con.left_inv] idpo :=
  pathover.rec_on r idpo

  definition eq_of_pathover {a' a₂' : A'} (q : a' =[p] a₂') : a' = a₂' :=
  by cases q;reflexivity

  definition pathover_of_eq [unfold 5 8] (p : a = a₂) {a' a₂' : A'} (q : a' = a₂') : a' =[p] a₂' :=
  by cases p;cases q;constructor

  definition pathover_constant [constructor] (p : a = a₂) (a' a₂' : A') : a' =[p] a₂' ≃ a' = a₂' :=
  begin
    fapply equiv.MK,
    { exact eq_of_pathover},
    { exact pathover_of_eq p},
    { intro r, cases p, cases r, reflexivity},
    { intro r, cases r, reflexivity},
  end

  definition pathover_of_eq_tr_constant_inv (p : a = a₂) (a' : A')
    : pathover_of_eq p (tr_constant p a')⁻¹ = pathover_tr p a' :=
  by cases p; constructor

  definition eq_of_pathover_idp [unfold 6] {b' : B a} (q : b =[idpath a] b') : b = b' :=
  tr_eq_of_pathover q

  --should B be explicit in the next two definitions?
  definition pathover_idp_of_eq [unfold 6] {b' : B a} (q : b = b') : b =[idpath a] b' :=
  pathover_of_tr_eq q

  definition pathover_idp [constructor] (b : B a) (b' : B a) : b =[idpath a] b' ≃ b = b' :=
  equiv.MK eq_of_pathover_idp
           (pathover_idp_of_eq)
           (to_right_inv !pathover_equiv_tr_eq)
           (to_left_inv !pathover_equiv_tr_eq)

  definition eq_of_pathover_idp_pathover_of_eq {A X : Type} (x : X) {a a' : A} (p : a = a') :
    eq_of_pathover_idp (pathover_of_eq (idpath x) p) = p :=
  by induction p; reflexivity

  -- definition pathover_idp (b : B a) (b' : B a) : b =[idpath a] b' ≃ b = b' :=
  -- pathover_equiv_tr_eq idp b b'

  -- definition eq_of_pathover_idp [reducible] {b' : B a} (q : b =[idpath a] b') : b = b' :=
  -- to_fun !pathover_idp q

  -- definition pathover_idp_of_eq [reducible] {b' : B a} (q : b = b') : b =[idpath a] b' :=
  -- to_inv !pathover_idp q

  definition idp_rec_on [recursor] [unfold 7] {P : Π⦃b₂ : B a⦄, b =[idpath a] b₂ → Type}
    {b₂ : B a} (r : b =[idpath a] b₂) (H : P idpo) : P r :=
  have H2 : P (pathover_idp_of_eq (eq_of_pathover_idp r)), from
    eq.rec_on (eq_of_pathover_idp r) H,
  proof left_inv !pathover_idp r ▸ H2 qed

  definition rec_on_right [recursor] {P : Π⦃b₂ : B a₂⦄, b =[p] b₂ → Type}
    {b₂ : B a₂} (r : b =[p] b₂) (H : P !pathover_tr) : P r :=
  by cases r; exact H

  definition rec_on_left [recursor] {P : Π⦃b : B a⦄, b =[p] b₂ → Type}
    {b : B a} (r : b =[p] b₂) (H : P !tr_pathover) : P r :=
  by cases r; exact H

  --pathover with fibration B' ∘ f
  definition pathover_ap [unfold 10] (B' : A' → Type) (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) : b =[ap f p] b₂ :=
  by cases q; constructor

  definition pathover_of_pathover_ap (B' : A' → Type) (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) : b =[p] b₂ :=
  by cases p; apply (idp_rec_on q); apply idpo

  definition pathover_compose [constructor] (B' : A' → Type) (f : A → A') (p : a = a₂)
    (b : B' (f a)) (b₂ : B' (f a₂)) : b =[p] b₂ ≃ b =[ap f p] b₂ :=
  begin
    fapply equiv.MK,
    { exact pathover_ap B' f},
    { exact pathover_of_pathover_ap B' f},
    { intro q, cases p, esimp, apply (idp_rec_on q), apply idp},
    { intro q, cases q, reflexivity},
  end

  definition pathover_of_pathover_tr (q : b =[p ⬝ p₂] p₂ ▸ b₂) : b =[p] b₂ :=
  pathover_cancel_right q !pathover_tr⁻¹ᵒ

  definition pathover_tr_of_pathover (q : b =[p₁₃ ⬝ p₂⁻¹] b₂) : b =[p₁₃] p₂ ▸ b₂ :=
  pathover_cancel_right' q !pathover_tr

  definition pathover_of_tr_pathover (q : p ▸ b =[p⁻¹ ⬝ p₁₃] b₃) : b =[p₁₃] b₃ :=
  pathover_cancel_left' !pathover_tr q

  definition tr_pathover_of_pathover (q : b =[p ⬝ p₂] b₃) : p ▸ b =[p₂] b₃ :=
  pathover_cancel_left !pathover_tr⁻¹ᵒ q

  definition pathover_tr_of_eq (q : b = b') : b =[p] p ▸ b' :=
  by cases q;apply pathover_tr

  definition tr_pathover_of_eq (q : b₂ = b₂') : p⁻¹ ▸ b₂ =[p] b₂' :=
  by cases q;apply tr_pathover

  variable (C)
  definition transporto (r : b =[p] b₂) (c : C b) : C b₂ :=
  by induction r;exact c
  infix ` ▸o `:75 := transporto _

  definition fn_tro_eq_tro_fn {C' : Π ⦃a : A⦄, B a → Type} (q : b =[p] b₂)
    (f : Π⦃a : A⦄ (b : B a), C b → C' b) (c : C b) : f b₂ (q ▸o c) = q ▸o (f b c) :=
  by induction q; reflexivity
  variable {C}

  /- various variants of ap for pathovers -/
  definition apd [unfold 6] (f : Πa, B a) (p : a = a₂) : f a =[p] f a₂ :=
  by induction p; constructor

  definition apo [unfold 12] {f : A → A'} (g : Πa, B a → B'' (f a)) (q : b =[p] b₂) :
    g a b =[p] g a₂ b₂ :=
  by induction q; constructor

  definition apd011 [unfold 10] (f : Πa, B a → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : f a b = f a₂ b₂ :=
  by cases Hb; reflexivity

  definition apd0111 [unfold 13 14] (f : Πa b, C b → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
    (Hc : c =[apd011 C Ha Hb] c₂) : f a b c = f a₂ b₂ c₂ :=
  by cases Hb; apply (idp_rec_on Hc); apply idp

  definition apod11 {f : Πb, C b} {g : Πb₂, C b₂} (r : f =[p] g)
    {b : B a} {b₂ : B a₂} (q : b =[p] b₂) : f b =[apd011 C p q] g b₂ :=
  by cases r; apply (idp_rec_on q); constructor

  definition apdo10 {f : Πb, C b} {g : Πb₂, C b₂} (r : f =[p] g)
    (b : B a) : f b =[apd011 C p !pathover_tr] g (p ▸ b) :=
  by cases r; constructor

  definition apo10 [unfold 9] {f : B a → B' a} {g : B a₂ → B' a₂} (r : f =[p] g)
    (b : B a) : f b =[p] g (p ▸ b) :=
  by cases r; constructor

  definition apo10_constant_right [unfold 9] {f : B a → A'} {g : B a₂ → A'} (r : f =[p] g)
    (b : B a) : f b = g (p ▸ b) :=
  by cases r; constructor

  definition apo10_constant_left [unfold 9] {f : A' → B a} {g : A' → B a₂} (r : f =[p] g)
    (a' : A') : f a' =[p] g a' :=
  by cases r; constructor

  definition apo11 {f : B a → B' a} {g : B a₂ → B' a₂} (r : f =[p] g)
    (q : b =[p] b₂) : f b =[p] g b₂ :=
  by induction q; exact apo10 r b

  definition apdo011 {A : Type} {B : A → Type} {C : Π⦃a⦄, B a → Type}
    (f : Π⦃a⦄ (b : B a), C b) {a a' : A} (p : a = a') {b : B a} {b' : B a'} (q : b =[p] b')
      : f b =[apd011 C p q] f b' :=
  by cases q; constructor

  definition apdo0111 {A : Type} {B : A → Type} {C C' : Π⦃a⦄, B a → Type}
    (f : Π⦃a⦄ {b : B a}, C b → C' b) {a a' : A} (p : a = a') {b : B a} {b' : B a'} (q : b =[p] b')
    {c : C b} {c' : C b'} (r : c =[apd011 C p q] c')
      : f c =[apd011 C' p q] f c' :=
  begin
    induction q, esimp at r, induction r using idp_rec_on, constructor
  end

  definition apo11_constant_right [unfold 12] {f : B a → A'} {g : B a₂ → A'}
    (q : f =[p] g) (r : b =[p] b₂) : f b = g b₂ :=
  eq_of_pathover (apo11 q r)

  /- properties about these "ap"s, transporto and pathover_ap -/
  definition apd_con (f : Πa, B a) (p : a = a₂) (q : a₂ = a₃)
    : apd f (p ⬝ q) = apd f p ⬝o apd f q :=
  by cases p; cases q; reflexivity

  definition apd_inv (f : Πa, B a) (p : a = a₂) : apd f p⁻¹ = (apd f p)⁻¹ᵒ :=
  by cases p; reflexivity

  definition apd_eq_pathover_of_eq_ap (f : A → A') (p : a = a₂) :
    apd f p = pathover_of_eq p (ap f p) :=
  eq.rec_on p idp

  definition apo_invo (f : Πa, B a → B' a) {Ha : a = a₂} (Hb : b =[Ha] b₂)
      : (apo f Hb)⁻¹ᵒ = apo f Hb⁻¹ᵒ :=
  by induction Hb; reflexivity

  definition apd011_inv (f : Πa, B a → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : (apd011 f Ha Hb)⁻¹ = (apd011 f Ha⁻¹ Hb⁻¹ᵒ) :=
  by induction Hb; reflexivity

  definition cast_apd011 (q : b =[p] b₂) (c : C b) : cast (apd011 C p q) c = q ▸o c :=
  by induction q; reflexivity

  definition apd_compose1 (g : Πa, B a → B' a) (f : Πa, B a) (p : a = a₂)
    : apd (g ∘' f) p = apo g (apd f p) :=
  by induction p; reflexivity

  definition apd_compose2 (g : Πa', B'' a') (f : A → A') (p : a = a₂)
    : apd (λa, g (f a)) p = pathover_of_pathover_ap B'' f (apd g (ap f p)) :=
  by induction p; reflexivity

  definition apo_tro (C : Π⦃a⦄, B' a → Type) (f : Π⦃a⦄, B a → B' a) (q : b =[p] b₂)
    (c : C (f b)) : apo f q ▸o c = q ▸o c :=
  by induction q; reflexivity

  definition pathover_ap_tro {B' : A' → Type} (C : Π⦃a'⦄, B' a' → Type) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) (c : C b) : pathover_ap B' f q ▸o c = q ▸o c :=
  by induction q; reflexivity

  definition pathover_ap_invo_tro {B' : A' → Type} (C : Π⦃a'⦄, B' a' → Type) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) (c : C b₂)
    : (pathover_ap B' f q)⁻¹ᵒ ▸o c = q⁻¹ᵒ ▸o c :=
  by induction q; reflexivity

  definition pathover_tro (q : b =[p] b₂) (c : C b) : c =[apd011 C p q] q ▸o c :=
  by induction q; constructor

  definition pathover_ap_invo {B' : A' → Type} (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂)
    : pathover_ap B' f q⁻¹ᵒ =[ap_inv f p] (pathover_ap B' f q)⁻¹ᵒ :=
  by induction q; exact idpo

  definition tro_invo_tro {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') (c : C b') :
    q ▸o (q⁻¹ᵒ ▸o c) = c :=
  by induction q; reflexivity

  definition invo_tro_tro {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') (c : C b) :
    q⁻¹ᵒ ▸o (q ▸o c) = c :=
  by induction q; reflexivity

  definition cono_tro {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a₁ a₂ a₃ : A} {p₁ : a₁ = a₂} {p₂ : a₂ = a₃} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (q₁ : b₁ =[p₁] b₂) (q₂ : b₂ =[p₂] b₃) (c : C b₁) :
    transporto C (q₁ ⬝o q₂) c = transporto C q₂ (transporto C q₁ c) :=
  by induction q₂; reflexivity

  definition is_equiv_transporto [constructor] {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') : is_equiv (transporto C q) :=
  begin
    fapply adjointify,
    { exact transporto C q⁻¹ᵒ},
    { exact tro_invo_tro C q},
    { exact invo_tro_tro C q}
  end

  definition equiv_apd011 [constructor] {A : Type} {B : A → Type} (C : Π⦃a⦄, B a → Type)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') : C b ≃ C b' :=
  equiv.mk (transporto C q) !is_equiv_transporto

  /- some cancellation laws for concato_eq an variants -/

  definition cono.right_inv_eq (q : b = b') :
    pathover_idp_of_eq q ⬝op q⁻¹ = (idpo : b =[refl a] b) :=
  by induction q;constructor

  definition cono.right_inv_eq' (q : b = b') :
    q ⬝po (pathover_idp_of_eq q⁻¹) = (idpo : b =[refl a] b) :=
  by induction q;constructor

  definition cono.left_inv_eq (q : b = b') :
    pathover_idp_of_eq q⁻¹ ⬝op q = (idpo : b' =[refl a] b') :=
  by induction q;constructor

  definition cono.left_inv_eq' (q : b = b') :
    q⁻¹ ⬝po pathover_idp_of_eq q = (idpo : b' =[refl a] b') :=
  by induction q;constructor

  definition pathover_of_fn_pathover_fn (f : Π{a}, B a ≃ B' a) (r : f b =[p] f b₂) : b =[p] b₂ :=
  (left_inv f b)⁻¹ ⬝po apo (λa, f⁻¹ᵉ) r ⬝op left_inv f b₂

  /- a pathover in a pathover type where the only thing which varies is the path is the same as
    an equality with a change_path -/
  definition change_path_of_pathover (s : p = p') (r : b =[p] b₂) (r' : b =[p'] b₂)
    (q : r =[s] r') : change_path s r = r' :=
  by induction s; eapply idp_rec_on q; reflexivity

  definition pathover_of_change_path (s : p = p') (r : b =[p] b₂) (r' : b =[p'] b₂)
    (q : change_path s r = r') : r =[s] r' :=
  by induction s; induction q; constructor

  definition pathover_pathover_path [constructor] (s : p = p') (r : b =[p] b₂) (r' : b =[p'] b₂) :
    (r =[s] r') ≃ change_path s r = r' :=
  begin
    fapply equiv.MK,
    { apply change_path_of_pathover},
    { apply pathover_of_change_path},
    { intro q, induction s, induction q, reflexivity},
    { intro q, induction s, eapply idp_rec_on q, reflexivity},
  end

  /- variants of inverse2 and concat2 -/
  definition inverseo2 [unfold 10] {r r' : b =[p] b₂} (s : r = r') : r⁻¹ᵒ = r'⁻¹ᵒ :=
  by induction s; reflexivity

  definition concato2 [unfold 15 16] {r r' : b =[p] b₂} {r₂ r₂' : b₂ =[p₂] b₃}
    (s : r = r') (s₂ : r₂ = r₂') : r ⬝o r₂ = r' ⬝o r₂' :=
  by induction s; induction s₂; reflexivity

  infixl ` ◾o `:75 := concato2
  postfix [parsing_only] `⁻²ᵒ`:(max+10) := inverseo2 --this notation is abusive, should we use it?

  -- find a better name for this
  definition fn_tro_eq_tro_fn2 (q : b =[p] b₂)
    {k : A → A} {l : Π⦃a⦄, B a → B (k a)} (m : Π⦃a⦄ {b : B a}, C b → C (l b))
    (c : C b) :
    m (q ▸o c) = (pathover_ap B k (apo l q)) ▸o (m c) :=
  by induction q; reflexivity

  definition apd0111_precompose (f  : Π⦃a⦄ {b : B a}, C b → A')
    {k : A → A} {l : Π⦃a⦄, B a → B (k a)} (m : Π⦃a⦄ {b : B a}, C b → C (l b))
    {q : b =[p] b₂} (c : C b)
    : apd0111 (λa b c, f (m c)) p q (pathover_tro q c) ⬝ ap (@f _ _) (fn_tro_eq_tro_fn2 q m c) =
      apd0111 f (ap k p) (pathover_ap B k (apo l q)) (pathover_tro _ (m c)) :=
  by induction q; reflexivity


end eq
