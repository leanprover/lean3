/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

The "equivalence closure" of a type-valued relation.
A more appropriate intuition is the type of words formed from the relation,
  and inverses, concatenations and reflexivity
-/

import algebra.relation eq2 arity cubical.pathover2

open eq equiv function

inductive e_closure {A : Type} (R : A → A → Type) : A → A → Type :=
| of_rel : Π{a a'} (r : R a a'), e_closure R a a'
| of_path : Π{a a'} (pp : a = a'), e_closure R a a'
| symm : Π{a a'} (r : e_closure R a a'), e_closure R a' a
| trans : Π{a a' a''} (r : e_closure R a a') (r' : e_closure R a' a''), e_closure R a a''

namespace e_closure
  infix ` ⬝r `:75 := e_closure.trans
  postfix `⁻¹ʳ`:(max+10) := e_closure.symm
  notation `[`:max a `]`:0 := e_closure.of_rel a
  notation `<`:max p `>`:0 := e_closure.of_path _ p
  abbreviation rfl [constructor] {A : Type} {R : A → A → Type} {a : A} := of_path R (idpath a)
end e_closure
open e_closure
namespace relation

section
  parameters {A : Type}
             {R : A → A → Type}
  local abbreviation T := e_closure R

  variables ⦃a a' a'' : A⦄ {s : R a a'} {r : T a a} {B C : Type}

  protected definition e_closure.elim [unfold 8] {f : A → B}
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a') : f a = f a' :=
  begin
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
      exact e r,
      exact ap f pp,
      exact IH⁻¹,
      exact IH₁ ⬝ IH₂
  end

  definition ap_e_closure_elim_h [unfold 12] {B C : Type} {f : A → B} {g : B → C}
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
    : ap g (e_closure.elim e t) = e_closure.elim e' t :=
  begin
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
      apply p,
      induction pp, reflexivity,
      exact ap_inv g (e_closure.elim e r) ⬝ inverse2 IH,
      exact ap_con g (e_closure.elim e r) (e_closure.elim e r') ⬝ (IH₁ ◾ IH₂)
  end

  definition ap_e_closure_elim_h_symm [unfold_full] {B C : Type} {f : A → B} {g : B → C}
    {e : Π⦃a a' : A⦄, R a a' → f a = f a'}
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a') :
    ap_e_closure_elim_h e p t⁻¹ʳ = ap_inv g (e_closure.elim e t) ⬝ (ap_e_closure_elim_h e p t)⁻² :=
  by reflexivity

  definition ap_e_closure_elim_h_trans [unfold_full] {B C : Type} {f : A → B} {g : B → C}
    {e : Π⦃a a' : A⦄, R a a' → f a = f a'}
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a') (t' : T a' a'')
    : ap_e_closure_elim_h e p (t ⬝r t') = ap_con g (e_closure.elim e t) (e_closure.elim e t') ⬝
      (ap_e_closure_elim_h e p t ◾ ap_e_closure_elim_h e p t') :=
  by reflexivity

  definition ap_e_closure_elim [unfold 10] {B C : Type} {f : A → B} (g : B → C)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
    : ap g (e_closure.elim e t) = e_closure.elim (λa a' r, ap g (e r)) t :=
  ap_e_closure_elim_h e (λa a' s, idp) t

  definition ap_e_closure_elim_symm [unfold_full] {B C : Type} {f : A → B} (g : B → C)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
    : ap_e_closure_elim g e t⁻¹ʳ = ap_inv g (e_closure.elim e t) ⬝ (ap_e_closure_elim g e t)⁻² :=
  by reflexivity

  definition ap_e_closure_elim_trans [unfold_full] {B C : Type} {f : A → B} (g : B → C)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a') (t' : T a' a'')
    : ap_e_closure_elim g e (t ⬝r t') = ap_con g (e_closure.elim e t) (e_closure.elim e t') ⬝
      (ap_e_closure_elim g e t ◾ ap_e_closure_elim g e t') :=
  by reflexivity

  definition e_closure_elim_eq [unfold 8] {f : A → B}
    {e e' : Π⦃a a' : A⦄, R a a' → f a = f a'} (p : e ~3 e') (t : T a a')
    : e_closure.elim e t = e_closure.elim e' t :=
  begin
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
      apply p,
      reflexivity,
      exact IH⁻²,
      exact IH₁ ◾ IH₂
  end

  -- TODO: formulate and prove this without using function extensionality,
  -- and modify the proofs using this to also not use function extensionality
  -- strategy: use `e_closure_elim_eq` instead of `ap ... (eq_of_homotopy3 p)`
  definition ap_e_closure_elim_h_eq {B C : Type} {f : A → B} {g : B → C}
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
    : ap_e_closure_elim_h e p t =
      ap_e_closure_elim g e t ⬝ ap (λx, e_closure.elim x t) (eq_of_homotopy3 p) :=
  begin
    fapply homotopy3.rec_on p,
    intro q, esimp at q, induction q,
    esimp, rewrite eq_of_homotopy3_id
  end

  theorem ap_ap_e_closure_elim_h {B C D : Type} {f : A → B}
    {g : B → C} (h : C → D)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
    : square (ap (ap h) (ap_e_closure_elim_h e p t))
             (ap_e_closure_elim_h e (λa a' s, ap_compose h g (e s)) t)
             (ap_compose h g (e_closure.elim e t))⁻¹
             (ap_e_closure_elim_h e' (λa a' s, (ap (ap h) (p s))⁻¹) t) :=
  begin
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
    { esimp,
      apply square_of_eq, exact !con.right_inv ⬝ !con.left_inv⁻¹},
    { induction pp, apply ids},
    { rewrite [▸*,ap_con (ap h)],
      refine (transpose !ap_compose_inv)⁻¹ᵛ ⬝h _,
      rewrite [con_inv,inv_inv,-inv2_inv],
      exact !ap_inv2 ⬝v square_inv2 IH},
    { rewrite [▸*,ap_con (ap h)],
      refine (transpose !ap_compose_con)⁻¹ᵛ ⬝h _,
      rewrite [con_inv,inv_inv,con2_inv],
      refine !ap_con2 ⬝v square_con2 IH₁ IH₂},
  end

  theorem ap_ap_e_closure_elim {B C D : Type} {f : A → B}
    (g : B → C) (h : C → D)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
    : square (ap (ap h) (ap_e_closure_elim g e t))
             (ap_e_closure_elim_h e (λa a' s, ap_compose h g (e s)) t)
             (ap_compose h g (e_closure.elim e t))⁻¹
             (ap_e_closure_elim   h (λa a' r, ap g (e r)) t) :=
  !ap_ap_e_closure_elim_h

  definition ap_e_closure_elim_h_zigzag {B C D : Type} {f : A → B}
    {g : B → C} (h : C → D)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → h (g (f a)) = h (g (f a'))}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap (h ∘ g) (e s) = e' s) (t : T a a')
    : ap_e_closure_elim   h (λa a' s, ap g (e s)) t ⬝
     (ap_e_closure_elim_h e (λa a' s, ap_compose h g (e s)) t)⁻¹ ⬝
      ap_e_closure_elim_h e p t =
      ap_e_closure_elim_h (λa a' s, ap g (e s)) (λa a' s, (ap_compose h g (e s))⁻¹ ⬝ p s) t :=
  begin
    refine whisker_right _ (eq_of_square (ap_ap_e_closure_elim g h e t)⁻¹ʰ)⁻¹ ⬝ _,
    refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con, apply eq_of_square,
    apply transpose,
    -- the rest of the proof is almost the same as the proof of ap_ap_e_closure_elim[_h].
    -- Is there a connection between these theorems?
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
    { esimp, apply square_of_eq, apply idp_con},
    { induction pp, apply ids},
    { rewrite [▸*,ap_con (ap h)],
      refine (transpose !ap_compose_inv)⁻¹ᵛ ⬝h _,
      rewrite [con_inv,inv_inv,-inv2_inv],
      exact !ap_inv2 ⬝v square_inv2 IH},
    { rewrite [▸*,ap_con (ap h)],
      refine (transpose !ap_compose_con)⁻¹ᵛ ⬝h _,
      rewrite [con_inv,inv_inv,con2_inv],
      refine !ap_con2 ⬝v square_con2 IH₁ IH₂},

  end

  definition is_equivalence_e_closure : is_equivalence T :=
  begin
    constructor,
      intro a, exact rfl,
      intro a a' t, exact t⁻¹ʳ,
      intro a a' a'' t t', exact t ⬝r t',
  end

  /- dependent elimination -/

  variables {P : B → Type} {Q : C → Type} {f : A → B} {g : B → C} {f' : Π(a : A), P (f a)}
  protected definition e_closure.elimo [unfold 11] (p : Π⦃a a' : A⦄, R a a' → f a = f a')
    (po : Π⦃a a' : A⦄ (s : R a a'), f' a =[p s] f' a') (t : T a a')
    : f' a =[e_closure.elim p t] f' a' :=
  begin
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
      exact po r,
      induction pp, constructor,
      exact IH⁻¹ᵒ,
      exact IH₁ ⬝o IH₂
  end

  definition elimo_symm [unfold_full] (p : Π⦃a a' : A⦄, R a a' → f a = f a')
    (po : Π⦃a a' : A⦄ (s : R a a'), f' a =[p s] f' a') (t : T a a')
    : e_closure.elimo p po t⁻¹ʳ = (e_closure.elimo p po t)⁻¹ᵒ :=
  by reflexivity

  definition elimo_trans [unfold_full] (p : Π⦃a a' : A⦄, R a a' → f a = f a')
    (po : Π⦃a a' : A⦄ (s : R a a'), f' a =[p s] f' a') (t : T a a') (t' : T a' a'')
    : e_closure.elimo p po (t ⬝r t') = e_closure.elimo p po t ⬝o e_closure.elimo p po t' :=
  by reflexivity

  definition ap_e_closure_elimo_h [unfold 12]  {g' : Πb, Q (g b)}
    (p : Π⦃a a' : A⦄, R a a' → f a = f a')
    (po : Π⦃a a' : A⦄ (s : R a a'), g' (f a) =[p s] g' (f a'))
    (q : Π⦃a a' : A⦄ (s : R a a'), apd g' (p s) = po s)
    (t : T a a') : apd g' (e_closure.elim p t) = e_closure.elimo p po t :=
  begin
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
      apply q,
      induction pp, reflexivity,
      esimp [e_closure.elim],
      exact apd_inv g' (e_closure.elim p r) ⬝ IH⁻²ᵒ,
      exact apd_con g' (e_closure.elim p r) (e_closure.elim p r') ⬝ (IH₁ ◾o IH₂)
  end

  theorem e_closure_elimo_ap {g' : Π(a : A), Q (g (f a))}
    (p : Π⦃a a' : A⦄, R a a' → f a = f a')
    (po : Π⦃a a' : A⦄ (s : R a a'), g' a =[ap g (p s)] g' a')
    (t : T a a') : e_closure.elimo p (λa a' s, pathover_of_pathover_ap Q g (po s)) t =
      pathover_of_pathover_ap Q g (change_path (ap_e_closure_elim g p t)⁻¹
        (e_closure.elimo (λa a' r, ap g (p r)) po t)) :=
  begin
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
    { reflexivity},
    { induction pp; reflexivity},
    { rewrite [+elimo_symm, ap_e_closure_elim_symm, IH, con_inv, change_path_con, ▸*, -inv2_inv,
               change_path_invo, pathover_of_pathover_ap_invo]},
    { rewrite [+elimo_trans, ap_e_closure_elim_trans, IH₁, IH₂, con_inv, change_path_con, ▸*,
               con2_inv, change_path_cono, pathover_of_pathover_ap_cono]},
  end

end
end relation
