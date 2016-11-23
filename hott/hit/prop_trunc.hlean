import function types.trunc hit.colimit homotopy.connectedness --types.nat.hott hit.trunc cubical.square

open eq is_trunc unit quotient seq_colim pi nat equiv sum algebra is_conn function

/-
  In this file we define the propositional truncation, which, given (X : Type)
  has constructors
  * tr             : X → trunc X
  * is_prop_trunc  : is_prop (trunc X)
  and with a recursor which recurses to any family of mere propositions.

  The construction uses a "one step truncation" of X, with two constructors:
  * tr    : X → one_step_tr X
  * tr_eq : Π(a b : X), tr a = tr b
  This is like a truncation, but taking out the recursive part.
  Martin Escardo calls this construction the generalized circle, since the one step truncation of the
    unit type is the circle.

  Then we can repeat this n times:
    A 0 = X,
    A (n + 1) = one_step_tr (A n)
  We have a map
    f {n : ℕ} : A n → A (n + 1) := tr
  Then trunc is defined as the sequential colimit of (A, f).

  Both the one step truncation and the sequential colimit can be defined as a quotient, which is a
  primitive HIT in Lean. Here, with a quotient, we mean the following HIT:
  Given {X : Type} (R : X → X → Type) we have the constructors
  * class_of  : X → quotient R
  * eq_of_rel : Π{a a' : X}, R a a' → a = a'

  See the comment below for a sketch of the proof that (trunc A) is actually a mere proposition.
-/

/- definition of "one step truncation" in terms of quotients -/

namespace one_step_tr
  section
  parameters {A : Type}
  variables (a a' : A)

  protected definition R (a a' : A) : Type₀ := unit
  parameter (A)
  definition one_step_tr : Type := quotient R
  parameter {A}
  definition tr : one_step_tr :=
  class_of R a

  definition tr_eq : tr a = tr a' :=
  eq_of_rel _ star

  protected definition rec {P : one_step_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (x : one_step_tr) : P x :=
  begin
    fapply (quotient.rec_on x),
    { intro a, apply Pt},
    { intro a a' H, cases H, apply Pe}
  end

  protected definition rec_on [reducible] {P : one_step_tr → Type} (x : one_step_tr)
    (Pt : Π(a : A), P (tr a)) (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') : P x :=
  rec Pt Pe x

  protected definition elim {P : Type} (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') (x : one_step_tr) : P :=
  rec Pt (λa a', pathover_of_eq _ (Pe a a')) x

  protected definition elim_on [reducible] {P : Type} (x : one_step_tr) (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') : P :=
  elim Pt Pe x

  theorem rec_tr_eq {P : one_step_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (a a' : A)
    : apd (rec Pt Pe) (tr_eq a a') = Pe a a' :=
  !rec_eq_of_rel

  theorem elim_tr_eq {P : Type} (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') (a a' : A)
    : ap (elim Pt Pe) (tr_eq a a') = Pe a a' :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (tr_eq a a')),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_tr_eq],
  end

  end

  definition n_step_tr [reducible] (A : Type) (n : ℕ) : Type :=
  nat.rec_on n A (λn' A', one_step_tr A')

end one_step_tr

attribute one_step_tr.rec one_step_tr.elim [recursor 5] [unfold 5]
attribute one_step_tr.rec_on one_step_tr.elim_on [unfold 2]
attribute one_step_tr.tr [constructor]

namespace one_step_tr
  /- Theorems about the one-step truncation -/
  open homotopy trunc prod
  theorem tr_eq_ne_idp {A : Type} (a : A) : tr_eq a a ≠ idp :=
  begin
    intro p,
    have H2 : Π{X : Type₁} {x : X} {q : x = x}, q = idp,
      from λX x q, calc
        q   = ap (one_step_tr.elim (λa, x) (λa b, q)) (tr_eq a a)               : elim_tr_eq
        ... = ap (one_step_tr.elim (λa, x) (λa b, q)) (refl (one_step_tr.tr a)) : by rewrite p
        ... = idp                                                               : idp,
    exact bool.eq_bnot_ne_idp H2
  end

  theorem tr_eq_ne_ap_tr {A : Type} {a b : A} (p : a = b) : tr_eq a b ≠ ap tr p :=
  by induction p; apply tr_eq_ne_idp

  theorem not_inhabited_set_trunc_one_step_tr (A : Type)
    : ¬(trunc 1 (one_step_tr A) × is_set (trunc 1 (one_step_tr A))) :=
  begin
    intro H, induction H with x H,
    refine trunc.elim_on x _, clear x, intro x,
    induction x,
    { have q : trunc -1 ((tr_eq a a) = idp),
      begin
        refine to_fun !tr_eq_tr_equiv _,
        refine @is_prop.elim _ _ _ _, apply is_trunc_equiv_closed, apply tr_eq_tr_equiv
      end,
      refine trunc.elim_on q _, clear q, intro p, exact !tr_eq_ne_idp p},
    { apply is_prop.elim}
  end

  theorem not_is_conn_one_step_tr (A : Type) : ¬is_conn 1 (one_step_tr A) :=
  λH, not_inhabited_set_trunc_one_step_tr A (!center, _)

  theorem is_prop_trunc_one_step_tr (A : Type) : is_prop (trunc 0 (one_step_tr A)) :=
  begin
    apply is_prop.mk,
    intro x y,
    refine trunc.rec_on x _, refine trunc.rec_on y _, clear x y, intro y x,
    induction x,
    { induction y,
      { exact ap trunc.tr !tr_eq},
      { apply is_prop.elimo}},
    { apply is_prop.elimo}
  end

  local attribute is_prop_trunc_one_step_tr [instance]

  theorem trunc_0_one_step_tr_equiv (A : Type) : trunc 0 (one_step_tr A) ≃ ∥ A ∥ :=
  begin
    apply equiv_of_is_prop,
    { intro x, refine trunc.rec _ x, clear x, intro x, induction x,
      { exact trunc.tr a},
      { apply is_prop.elim}},
    { intro x, refine trunc.rec _ x, clear x, intro a, exact trunc.tr (tr a)},
  end

  definition one_step_tr_functor [unfold 4] {A B : Type} (f : A → B) (x : one_step_tr A)
    : one_step_tr B :=
  begin
    induction x,
    { exact tr (f a)},
    { apply tr_eq}
  end

  definition one_step_tr_universal_property [constructor] (A B : Type)
    : (one_step_tr A → B) ≃ Σ(f : A → B), Π(x y : A), f x = f y :=
  begin
    fapply equiv.MK,
    { intro f, fconstructor, intro a, exact f (tr a), intros, exact ap f !tr_eq},
    { intro v a, induction v with f p, induction a, exact f a, apply p},
    { intro v, induction v with f p, esimp, apply ap (sigma.mk _), apply eq_of_homotopy2,
      intro a a', apply elim_tr_eq},
    { intro f, esimp, apply eq_of_homotopy, intro a, induction a,
        reflexivity,
        apply eq_pathover, apply hdeg_square, rewrite [▸*,elim_tr_eq]},
  end


end one_step_tr
open one_step_tr

namespace prop_trunc
namespace hide
  section
  parameter {X : Type}

  /- basic constructors -/
  definition A [reducible] (n : ℕ) : Type := nat.rec_on n X (λn' X', one_step_tr X')
  definition f [reducible] ⦃n : ℕ⦄ (a : A n) : A (succ n)                 := tr a
  definition f_eq [reducible] {n : ℕ} (a a' : A n) : f a = f a'   := tr_eq a a'
  definition truncX [reducible] : Type                                    := @seq_colim A f
  definition i [reducible] {n : ℕ} (a : A n) : truncX                     := inclusion f a
  definition g [reducible] {n : ℕ} (a : A n) : i (f a) = i a      := glue f a

  /- defining the normal recursor is easy -/
  definition rec {P : truncX → Type} [Pt : Πx, is_prop (P x)]
    (H : Π(a : X), P (@i 0 a)) (x : truncX) : P x :=
  begin
    induction x,
    { induction n with n IH,
      { exact H a},
      { induction a,
        { exact !g⁻¹ ▸ IH a},
        { apply is_prop.elimo}}},
    { apply is_prop.elimo}
  end

  /-
    The main effort is to prove that truncX is a mere proposition.
    We prove
      Π(a b : truncX), a = b
    first by induction on a, using the induction principle we just proven and then by induction on b

    On the point level we need to construct
      (1) a : A n, b : A m ⊢ p a b : i a = i b
    On the path level (for the induction on b) we need to show that
      (2) a : A n, b : A m ⊢ p a (f b) ⬝ g b = p a b
    The path level for a is automatic, since (Πb, a = b) is a mere proposition
    Thanks to Egbert Rijke for pointing this out

    For (1) we distinguish the cases n ≤ m and n ≥ m,
      and we prove that the two constructions coincide for n = m

    For (2) we distinguish the cases n ≤ m and n > m

    During the proof we heavily use induction on inequalities.
    (n ≤ m), or (le n m), is defined as an inductive family:
      inductive le (n : ℕ) : ℕ → Type₀ :=
      | refl : le n n
      | step : Π {m}, le n m → le n (succ m)
  -/


  /- point operations -/

  definition fr [reducible] [unfold 2] (n : ℕ) (a : X) : A n :=
  begin
    induction n with n x,
    { exact a},
    { exact f x},
  end

  /- path operations -/

  definition i_fr [unfold 2] (n : ℕ) (a : X) : i (fr n a) = @i 0 a :=
  begin
    induction n with n p,
    { reflexivity},
    { exact g (fr n a) ⬝ p},
  end

  definition eq_same {n : ℕ} (a a' : A n) : i a = i a' :=
  calc
    i a = i (f a)  : g
    ... = i (f a') : ap i (f_eq a a')
    ... = i a'     : g

  definition eq_constructors {n : ℕ} (a : X) (b : A n) : @i 0 a = i b :=
  calc
    i a = i (fr n a) : i_fr
    ... = i b        : eq_same

  /- 2-dimensional path operations -/

  theorem ap_i_ap_f {n : ℕ} {a a' : A n} (p : a = a') : !g⁻¹ ⬝ ap i (ap !f p) ⬝ !g = ap i p :=
  by induction p; apply con.left_inv

  theorem ap_i_eq_ap_i_same {n : ℕ} {a a' : A n} (p q : a = a') : ap i p = ap i q :=
  @(is_weakly_constant_ap i) eq_same a a' p q

  theorem ap_f_eq_f {n : ℕ} (a a' : A n)
    : !g⁻¹ ⬝ ap i (f_eq (f a) (f a')) ⬝ !g = ap i (f_eq a a') :=
  ap _ !ap_i_eq_ap_i_same ⬝ !ap_i_ap_f

  theorem eq_same_f {n : ℕ} (a a' : A n)
    : (g a)⁻¹ ⬝ eq_same (f a) (f a') ⬝ g a' = eq_same a a' :=
  begin
   esimp [eq_same],
   apply (ap (λx, _ ⬝ x ⬝ _)),
   apply (ap_f_eq_f a a'),
  end

  theorem eq_constructors_comp {n : ℕ} (a : X) (b : A n)
    : eq_constructors a (f b) ⬝ g b  = eq_constructors a b :=
  begin
    rewrite [↑eq_constructors,▸*,↓fr n a,↓i_fr n a,con_inv,+con.assoc],
    apply ap (λx, _ ⬝ x),
    rewrite -con.assoc, exact !eq_same_f
  end

  theorem is_prop_truncX : is_prop truncX :=
  begin
    apply is_prop_of_imp_is_contr,
    intro a,
    refine @rec _ _ _ a,
    clear a, intro a,
    fapply is_contr.mk,
    exact @i 0 a,
    intro b,
    induction b with n b n b,
    { apply eq_constructors},
    { apply (equiv.to_inv !eq_pathover_equiv_r), apply eq_constructors_comp}
  end

  end
end hide
end prop_trunc

namespace prop_trunc
  open hide
  definition ptrunc.{u} (A : Type.{u}) : Type.{u}            := @truncX A
  definition ptr {A : Type} : A → ptrunc A                   := @i A 0
  definition is_prop_trunc (A : Type) : is_prop (ptrunc A)   := is_prop_truncX
  protected definition ptrunc.rec {A : Type} {P : ptrunc A → Type}
    [Pt : Π(x : ptrunc A), is_prop (P x)]
    (H : Π(a : A), P (ptr a)) : Π(x : ptrunc A), P x          := @rec A P Pt H

  example {A : Type} {P : ptrunc A → Type} [Pt : Πaa, is_prop (P aa)]
          (H : Πa, P (ptr a)) (a : A) : (ptrunc.rec H) (ptr a) = H a := by reflexivity

  open sigma prod

  -- the constructed truncation is equivalent to the "standard" propositional truncation
  -- (called _root_.trunc -1 below)
  open trunc
  attribute is_prop_trunc [instance]
  definition ptrunc_equiv_trunc (A : Type) : ptrunc A ≃ trunc -1 A :=
  begin
    fapply equiv.MK,
    { intro x, induction x using ptrunc.rec with a, exact tr a},
    { intro x, refine trunc.rec _ x, intro a, exact ptr a},
    { intro x, induction x with a, reflexivity},
    { intro x, induction x using ptrunc.rec with a, reflexivity}
  end

  -- some other recursors we get from this construction:
  definition trunc.elim2 {A P : Type} (h : Π{n}, n_step_tr A n → P)
    (coh : Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a) (x : ptrunc A) : P :=
  begin
    induction x,
    { exact h a},
    { apply coh}
  end

  definition trunc.rec2 {A : Type} {P : truncX → Type} (h : Π{n} (a : n_step_tr A n), P (i a))
    (coh : Π(n : ℕ) (a : n_step_tr A n), h (f a) =[g a] h a)
    (x : ptrunc A) : P x :=
  begin
    induction x,
    { exact h a},
    { apply coh}
  end

  definition elim2_equiv [constructor] (A P : Type) : (ptrunc A → P) ≃
    Σ(h : Π{n}, n_step_tr A n → P),
      Π(n : ℕ) (a : n_step_tr A n), @h (succ n) (one_step_tr.tr a) = h a :=
  begin
    fapply equiv.MK,
    { intro h, fconstructor,
      { intro n a, refine h (i a)},
      { intro n a, exact ap h (g a)}},
    { intro x a, induction x with h p, induction a,
        exact h a,
        apply p},
    { intro x, induction x with h p, fapply sigma_eq,
      { reflexivity},
      { esimp, apply pathover_idp_of_eq, apply eq_of_homotopy2, intro n a, xrewrite elim_glue}},
    { intro h, apply eq_of_homotopy, intro a, esimp, induction a,
        esimp,
        apply eq_pathover, apply hdeg_square, esimp, rewrite elim_glue}
  end

  open sigma.ops
  definition conditionally_constant_equiv {A P : Type} (k : A → P) :
    (Σ(g : ptrunc A → P), Πa, g (ptr a) = k a) ≃
      Σ(h : Π{n}, n_step_tr A n → P),
        (Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a) × (Πa, @h 0 a = k a) :=
  calc
    (Σ(g : ptrunc A → P), Πa, g (ptr a) = k a)
      ≃ Σ(v : Σ(h : Π{n}, n_step_tr A n → P), Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a),
          Πa, (v.1) 0 a = k a
                    : sigma_equiv_sigma !elim2_equiv (λg, equiv.rfl)
  ... ≃ Σ(h : Π{n}, n_step_tr A n → P) (p : Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a),
          Πa, @h 0 a = k a
                    : sigma_assoc_equiv
  ... ≃ Σ(h : Π{n}, n_step_tr A n → P),
          (Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a) × (Πa, @h 0 a = k a)
                    : sigma_equiv_sigma_right (λa, !equiv_prod)

  definition cocone_of_is_collapsible {A : Type} (f : A → A) (p : Πa a', f a = f a')
    (n : ℕ) (x : n_step_tr A n) : A :=
  begin
    apply f,
    induction n with n h,
    { exact x},
    { apply to_inv !one_step_tr_universal_property ⟨f, p⟩, exact one_step_tr_functor h x}
  end

  definition has_split_support_of_is_collapsible {A : Type} (f : A → A) (p : Πa a', f a = f a')
    : ptrunc A → A :=
  begin
    fapply to_inv !elim2_equiv,
    fconstructor,
    { exact cocone_of_is_collapsible f p},
    { intro n a, apply p}

  end

end prop_trunc

open prop_trunc trunc
-- Corollaries for the actual truncation.
namespace is_trunc
  local attribute is_prop_trunc_one_step_tr [instance]
  definition is_prop.elim_set {A : Type} {P : Type} [is_set P] (f : A → P)
    (p : Πa a', f a = f a') (x : trunc -1 A) : P :=
  begin
    have y : trunc 0 (one_step_tr A),
    by induction x; exact trunc.tr (one_step_tr.tr a),
    induction y with y,
    induction y,
    { exact f a},
    { exact p a a'}
  end

  definition is_prop.elim_set_tr {A : Type} {P : Type} {H : is_set P} (f : A → P)
    (p : Πa a', f a = f a') (a : A) : is_prop.elim_set f p (tr a) = f a :=
  by reflexivity

end is_trunc
