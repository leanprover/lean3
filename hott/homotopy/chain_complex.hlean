/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Chain complexes.

We define chain complexes in a general way as a sequence X of types indexes over an arbitrary type
N with a successor S. There are maps X (S n) → X n for n : N. We can vary N to have chain complexes
indexed by ℕ, ℤ, a finite type or something else, and for both ℕ and ℤ we can choose the maps to
go up or down. We also use the indexing ℕ × 3 for the LES of homotopy groups, because then it
computes better (see [LES_of_homotopy_groups]).

We have two separate notions of
chain complexes:
- type_chain_complex: sequence of types, where exactness is formulated using pure existence.
- chain_complex: sequence of sets, where exactness is formulated using mere existence.

-/

import types.int algebra.group_theory types.fin types.unit

open eq pointed int unit is_equiv equiv is_trunc trunc function algebra group sigma.ops
     sum prod nat bool fin

structure succ_str : Type :=
  (carrier : Type)
  (succ : carrier → carrier)

attribute succ_str.carrier [coercion]

definition succ_str.S {X : succ_str} : X → X := succ_str.succ X

open succ_str

definition snat [reducible] [constructor] : succ_str := succ_str.mk ℕ nat.succ
definition snat' [reducible] [constructor] : succ_str := succ_str.mk ℕ nat.pred
definition sint [reducible] [constructor] : succ_str := succ_str.mk ℤ int.succ
definition sint' [reducible] [constructor] : succ_str := succ_str.mk ℤ int.pred

notation `+ℕ` := snat
notation `-ℕ` := snat'
notation `+ℤ` := sint
notation `-ℤ` := sint'

definition stratified_type [reducible] (N : succ_str) (n : ℕ) : Type₀ := N × fin (succ n)

definition stratified_succ {N : succ_str} {n : ℕ} (x : stratified_type N n)
  : stratified_type N n :=
(if val (pr2 x) = n then S (pr1 x) else pr1 x, cyclic_succ (pr2 x))

definition stratified [reducible] [constructor] (N : succ_str) (n : ℕ) : succ_str :=
succ_str.mk (stratified_type N n) stratified_succ

notation `+3ℕ` := stratified +ℕ 2
notation `-3ℕ` := stratified -ℕ 2
notation `+3ℤ` := stratified +ℤ 2
notation `-3ℤ` := stratified -ℤ 2
notation `+6ℕ` := stratified +ℕ 5
notation `-6ℕ` := stratified -ℕ 5
notation `+6ℤ` := stratified +ℤ 5
notation `-6ℤ` := stratified -ℤ 5

namespace succ_str
  protected definition add [reducible] {N : succ_str} (n : N) (k : ℕ) : N :=
  iterate S k n

  infix ` +' `:65 := succ_str.add

  definition add_succ {N : succ_str} (n : N) (k : ℕ) : n +' (k + 1) = (S n) +' k :=
  by induction k with k p; reflexivity; exact ap S p

end succ_str

namespace chain_complex

  export [notation] succ_str

  /-
    We define "type chain complexes" which are chain complexes without the
    "set"-requirement. Exactness is formulated without propositional truncation.
  -/
  structure type_chain_complex (N : succ_str) : Type :=
    (car : N → Type*)
    (fn : Π(n : N), car (S n) →* car n)
    (is_chain_complex : Π(n : N) (x : car (S (S n))), fn n (fn (S n) x) = pt)

  section
  variables {N : succ_str} (X : type_chain_complex N) (n : N)
  definition tcc_to_car [unfold 2] [coercion] := @type_chain_complex.car
  definition tcc_to_fn  [unfold 2] : X (S n) →* X n := type_chain_complex.fn X n
  definition tcc_is_chain_complex  [unfold 2]
    : Π(x : X (S (S n))), tcc_to_fn X n (tcc_to_fn X (S n) x) = pt :=
  type_chain_complex.is_chain_complex X n

  -- important: these notions are shifted by one! (this is to avoid transports)
  definition is_exact_at_t [reducible] /- X n -/ : Type :=
  Π(x : X (S n)), tcc_to_fn X n x = pt → fiber (tcc_to_fn X (S n)) x

  definition is_exact_t [reducible] /- X -/ : Type :=
  Π(n : N), is_exact_at_t X n

  -- A chain complex on +ℕ can be trivially extended to a chain complex on +ℤ
  definition type_chain_complex_from_left (X : type_chain_complex +ℕ)
    : type_chain_complex +ℤ :=
  type_chain_complex.mk (int.rec X (λn, punit))
    begin
      intro n, fconstructor,
      { induction n with n n,
        { exact tcc_to_fn X n},
        { esimp, intro x, exact star}},
      { induction n with n n,
        { apply respect_pt},
        { reflexivity}}
    end
    begin
      intro n, induction n with n n,
      { exact tcc_is_chain_complex X n},
      { esimp, intro x, reflexivity}
    end

  definition is_exact_t_from_left {X : type_chain_complex +ℕ} {n : ℕ}
    (H : is_exact_at_t X n)
    : is_exact_at_t (type_chain_complex_from_left X) (of_nat n) :=
  H

  /-
    Given a natural isomorphism between a chain complex and any other sequence,
    we can give the other sequence the structure of a chain complex, which is exact at the
    positions where the original sequence is.
  -/
  definition transfer_type_chain_complex [constructor] /- X -/
    {Y : N → Type*} (g : Π{n : N}, Y (S n) →* Y n) (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (S n)), e (tcc_to_fn X n x) = g (e x)) : type_chain_complex N :=
  type_chain_complex.mk Y @g
    abstract begin
      intro n, apply equiv_rect (equiv_of_pequiv e), intro x,
      refine ap g (p x)⁻¹ ⬝ _,
      refine (p _)⁻¹ ⬝ _,
      refine ap e (tcc_is_chain_complex X n _) ⬝ _,
      apply respect_pt
    end end

  theorem is_exact_at_t_transfer {X : type_chain_complex N} {Y : N → Type*}
    {g : Π{n : N}, Y (S n) →* Y n} (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (S n)), e (tcc_to_fn X n x) = g (e x)) {n : N}
    (H : is_exact_at_t X n) : is_exact_at_t (transfer_type_chain_complex X @g @e @p) n :=
  begin
    intro y q, esimp at *,
    have H2 : tcc_to_fn X n (e⁻¹ᵉ* y) = pt,
    begin
      refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
      refine ap _ q ⬝ _,
      exact respect_pt e⁻¹ᵉ*
    end,
    cases (H _ H2) with x r,
    refine fiber.mk (e x) _,
    refine (p x)⁻¹ ⬝ _,
    refine ap e r ⬝ _,
    apply right_inv
  end

  /-
    We want a theorem which states that if we have a chain complex, but with some
    where the maps are composed by an equivalences, we want to remove this equivalence.
    The following two theorems give sufficient conditions for when this is allowed.
    We use this to transform the LES of homotopy groups where on the odd levels we have
    maps -πₙ(...) into the LES of homotopy groups where we remove the minus signs (which
    represents composition with path inversion).
  -/
  definition type_chain_complex_cancel_aut [constructor] /- X -/
    (g : Π{n : N}, X (S n) →* X n) (e : Π{n}, X n ≃* X n)
    (r : Π{n}, X n →* X n)
    (p : Π{n : N} (x : X (S n)), g (e x) = tcc_to_fn X n x)
    (pr : Π{n : N} (x : X (S n)), g x = r (g (e x))) : type_chain_complex N :=
  type_chain_complex.mk X @g
    abstract begin
      have p' : Π{n : N} (x : X (S n)), g x = tcc_to_fn X n (e⁻¹ x),
      from λn, homotopy_inv_of_homotopy_pre e _ _ p,
      intro n x,
      refine ap g !p' ⬝ !pr ⬝ _,
      refine ap r !p ⬝ _,
      refine ap r (tcc_is_chain_complex X n _) ⬝ _,
      apply respect_pt
    end end

  theorem is_exact_at_t_cancel_aut {X : type_chain_complex N}
    {g : Π{n : N}, X (S n) →* X n} {e : Π{n}, X n ≃* X n}
    {r : Π{n}, X n →* X n} (l : Π{n}, X n →* X n)
    (p : Π{n : N} (x : X (S n)), g (e x) = tcc_to_fn X n x)
    (pr : Π{n : N} (x : X (S n)), g x = r (g (e x)))
    (pl : Π{n : N} (x : X (S n)), g (l x) = e (g x))
    (H : is_exact_at_t X n) : is_exact_at_t (type_chain_complex_cancel_aut X @g @e @r @p @pr) n :=
  begin
    intro y q, esimp at *,
    have H2 : tcc_to_fn X n (e⁻¹ y) = pt,
    from (homotopy_inv_of_homotopy_pre e _ _ p _)⁻¹ ⬝ q,
    cases (H _ H2) with x s,
    refine fiber.mk (l (e x)) _,
    refine !pl ⬝ _,
    refine ap e (!p ⬝ s) ⬝ _,
    apply right_inv
  end

  /-
    A more general transfer theorem.
    Here the base type can also change by an equivalence.
  -/
  definition transfer_type_chain_complex2 [constructor] {M : succ_str} {Y : M → Type*}
    (f : M ≃ N) (c : Π(m : M), S (f m) = f (S m))
    (g : Π{m : M}, Y (S m) →* Y m) (e : Π{m}, X (f m) ≃* Y m)
    (p : Π{m} (x : X (S (f m))), e (tcc_to_fn X (f m) x) = g (e (cast (ap (λx, X x) (c m)) x)))
    : type_chain_complex M :=
  type_chain_complex.mk Y @g
    begin
      intro m,
      apply equiv_rect (equiv_of_pequiv e),
      apply equiv_rect (equiv_of_eq (ap (λx, X x) (c (S m)))), esimp,
      apply equiv_rect (equiv_of_eq (ap (λx, X (S x)) (c m))), esimp,
      intro x, refine ap g (p _)⁻¹ ⬝ _,
      refine ap g (ap e (fn_cast_eq_cast_fn (c m) (tcc_to_fn X) x)) ⬝ _,
      refine (p _)⁻¹ ⬝ _,
      refine ap e (tcc_is_chain_complex X (f m) _) ⬝ _,
      apply respect_pt
    end

  definition is_exact_at_t_transfer2 {X : type_chain_complex N} {M : succ_str} {Y : M → Type*}
    (f : M ≃ N) (c : Π(m : M), S (f m) = f (S m))
    (g : Π{m : M}, Y (S m) →* Y m) (e : Π{m}, X (f m) ≃* Y m)
    (p : Π{m} (x : X (S (f m))), e (tcc_to_fn X (f m) x) = g (e (cast (ap (λx, X x) (c m)) x)))
    {m : M} (H : is_exact_at_t X (f m))
    : is_exact_at_t (transfer_type_chain_complex2 X f c @g @e @p) m :=
  begin
    intro y q, esimp at *,
    have H2 : tcc_to_fn X (f m) ((equiv_of_eq (ap (λx, X x) (c m)))⁻¹ᵉ (e⁻¹ y)) = pt,
    begin
      refine _ ⬝ ap e⁻¹ᵉ* q ⬝ (respect_pt (e⁻¹ᵉ*)), apply eq_inv_of_eq, clear q, revert y,
      apply inv_homotopy_of_homotopy_pre e,
      apply inv_homotopy_of_homotopy_pre, apply p
    end,
    induction (H _ H2) with x r,
    refine fiber.mk (e (cast (ap (λx, X x) (c (S m))) (cast (ap (λx, X (S x)) (c m)) x))) _,
    refine (p _)⁻¹ ⬝ _,
    refine ap e (fn_cast_eq_cast_fn (c m) (tcc_to_fn X) x) ⬝ _,
    refine ap (λx, e (cast _ x)) r ⬝ _,
    esimp [equiv.symm], rewrite [-ap_inv],
    refine ap e !cast_cast_inv ⬝ _,
    apply right_inv
  end

  end

  /- actual (set) chain complexes -/
  structure chain_complex (N : succ_str) : Type :=
    (car : N → Set*)
    (fn : Π(n : N), car (S n) →* car n)
    (is_chain_complex : Π(n : N) (x : car (S (S n))), fn n (fn (S n) x) = pt)

  section
  variables {N : succ_str} (X : chain_complex N) (n : N)

  definition cc_to_car [unfold 2] [coercion] := @chain_complex.car
  definition cc_to_fn  [unfold 2] : X (S n) →* X n := @chain_complex.fn N X n
  definition cc_is_chain_complex  [unfold 2]
    : Π(x : X (S (S n))), cc_to_fn X n (cc_to_fn X (S n) x) = pt :=
  @chain_complex.is_chain_complex N X n

  -- important: these notions are shifted by one! (this is to avoid transports)
  definition is_exact_at [reducible] /- X n -/ : Type :=
  Π(x : X (S n)), cc_to_fn X n x = pt → image (cc_to_fn X (S n)) x

  definition is_exact [reducible] /- X -/ : Type := Π(n : N), is_exact_at X n

  definition chain_complex_from_left (X : chain_complex +ℕ) : chain_complex +ℤ :=
  chain_complex.mk (int.rec X (λn, punit))
    begin
      intro n, fconstructor,
      { induction n with n n,
        { exact cc_to_fn X n},
        { esimp, intro x, exact star}},
      { induction n with n n,
        { apply respect_pt},
        { reflexivity}}
    end
    begin
      intro n, induction n with n n,
      { exact cc_is_chain_complex X n},
      { esimp, intro x, reflexivity}
    end

  definition is_exact_from_left {X : chain_complex +ℕ} {n : ℕ} (H : is_exact_at X n)
    : is_exact_at (chain_complex_from_left X) (of_nat n) :=
  H

  definition transfer_chain_complex [constructor] {Y : N → Set*}
    (g : Π{n : N}, Y (S n) →* Y n) (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (S n)), e (cc_to_fn X n x) = g (e x)) : chain_complex N :=
  chain_complex.mk Y @g
    abstract begin
      intro n, apply equiv_rect (equiv_of_pequiv e), intro x,
      refine ap g (p x)⁻¹ ⬝ _,
      refine (p _)⁻¹ ⬝ _,
      refine ap e (cc_is_chain_complex X n _) ⬝ _,
      apply respect_pt
    end end

  theorem is_exact_at_transfer {X : chain_complex N} {Y : N → Set*}
    (g : Π{n : N}, Y (S n) →* Y n) (e : Π{n}, X n ≃* Y n)
    (p : Π{n} (x : X (S n)), e (cc_to_fn X n x) = g (e x))
    {n : N} (H : is_exact_at X n) : is_exact_at (transfer_chain_complex X @g @e @p) n :=
  begin
    intro y q, esimp at *,
    have H2 : cc_to_fn X n (e⁻¹ᵉ* y) = pt,
    begin
      refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
      refine ap _ q ⬝ _,
      exact respect_pt e⁻¹ᵉ*
    end,
    induction (H _ H2) with x r,
    refine image.mk (e x) _,
    refine (p x)⁻¹ ⬝ _,
    refine ap e r ⬝ _,
    apply right_inv
  end

  /- A type chain complex can be set-truncated to a chain complex -/
  definition trunc_chain_complex [constructor] (X : type_chain_complex N)
    : chain_complex N :=
  chain_complex.mk
    (λn, ptrunc 0 (X n))
    (λn, ptrunc_functor 0 (tcc_to_fn X n))
    begin
      intro n x, esimp at *,
      refine @trunc.rec _ _ _ (λH, !is_trunc_eq) _ x,
      clear x, intro x, esimp,
      exact ap tr (tcc_is_chain_complex X n x)
    end

  definition is_exact_at_trunc (X : type_chain_complex N) {n : N}
    (H : is_exact_at_t X n) : is_exact_at (trunc_chain_complex X) n :=
  begin
    intro x p, esimp at *,
    induction x with x, esimp at *,
    note q := !tr_eq_tr_equiv p,
    induction q with q,
    induction H x q with y r,
    refine image.mk (tr y) _,
    esimp, exact ap tr r
  end

  definition transfer_chain_complex2 [constructor] {M : succ_str} {Y : M → Set*}
    (f : N ≃ M) (c : Π(n : N), f (S n) = S (f n))
    (g : Π{m : M}, Y (S m) →* Y m) (e : Π{n}, X n ≃* Y (f n))
    (p : Π{n} (x : X (S n)), e (cc_to_fn X n x) = g (c n ▸ e x)) : chain_complex M :=
  chain_complex.mk Y @g
    begin
      refine equiv_rect f _ _, intro n,
      have H : Π (x : Y (f (S (S n)))), g (c n ▸ g (c (S n) ▸ x)) = pt,
      begin
        apply equiv_rect (equiv_of_pequiv e), intro x,
        refine ap (λx, g (c n ▸ x)) (@p (S n) x)⁻¹ᵖ ⬝ _,
        refine (p _)⁻¹ ⬝ _,
        refine ap e (cc_is_chain_complex X n _) ⬝ _,
        apply respect_pt
      end,
      refine pi.pi_functor _ _ H,
      { intro x, exact (c (S n))⁻¹ ▸ (c n)⁻¹ ▸ x}, -- with implicit arguments, this is:
      -- transport (λx, Y x) (c (S n))⁻¹ (transport (λx, Y (S x)) (c n)⁻¹ x)
      { intro x, intro p, refine _ ⬝ p, rewrite [tr_inv_tr, fn_tr_eq_tr_fn (c n)⁻¹ @g, tr_inv_tr]}
    end

  definition is_exact_at_transfer2 {X : chain_complex N} {M : succ_str} {Y : M → Set*}
    (f : N ≃ M) (c : Π(n : N), f (S n) = S (f n))
    (g : Π{m : M}, Y (S m) →* Y m) (e : Π{n}, X n ≃* Y (f n))
    (p : Π{n} (x : X (S n)), e (cc_to_fn X n x) = g (c n ▸ e x))
    {n : N} (H : is_exact_at X n) : is_exact_at (transfer_chain_complex2 X f c @g @e @p) (f n) :=
  begin
    intro y q, esimp at *,
    have H2 : cc_to_fn X n (e⁻¹ᵉ* ((c n)⁻¹ ▸ y)) = pt,
    begin
      refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
      rewrite [tr_inv_tr, q],
      exact respect_pt e⁻¹ᵉ*
    end,
    induction (H _ H2) with x r,
    refine image.mk (c n ▸ c (S n) ▸ e x) _,
    rewrite [fn_tr_eq_tr_fn (c n) @g],
    refine ap (λx, c n ▸ x) (p x)⁻¹ ⬝ _,
    refine ap (λx, c n ▸ e x) r ⬝ _,
    refine ap (λx, c n ▸ x) !right_inv ⬝ _,
    apply tr_inv_tr,
  end

  /-
    This is a start of a development of chain complexes consisting only on groups.
    This might be useful to have in stable algebraic topology, but in the unstable case it's less
    useful, since the smallest terms usually don't have a group structure.
    We don't use it yet, so it's commented out for now
  -/
  -- structure group_chain_complex : Type :=
  --   (car : N → Group)
  --   (fn : Π(n : N), car (S n) →g car n)
  --   (is_chain_complex : Π{n : N} (x : car ((S n) + 1)), fn n (fn (S n) x) = 1)

  -- structure group_chain_complex : Type := -- chain complex on the naturals with maps going down
  --   (car : N → Group)
  --   (fn : Π(n : N), car (S n) →g car n)
  --   (is_chain_complex : Π{n : N} (x : car ((S n) + 1)), fn n (fn (S n) x) = 1)

  -- structure right_group_chain_complex : Type := -- chain complex on the naturals with maps going up
  --   (car : N → Group)
  --   (fn : Π(n : N), car n →g car (S n))
  --   (is_chain_complex : Π{n : N} (x : car n), fn (S n) (fn n x) = 1)

  -- definition  gcc_to_car [unfold 1] [coercion] := @group_chain_complex.car
  -- definition  gcc_to_fn  [unfold 1]            := @group_chain_complex.fn
  -- definition  gcc_is_chain_complex  [unfold 1] := @group_chain_complex.is_chain_complex
  -- definition lgcc_to_car [unfold 1] [coercion] := @left_group_chain_complex.car
  -- definition lgcc_to_fn  [unfold 1]            := @left_group_chain_complex.fn
  -- definition lgcc_is_chain_complex  [unfold 1] := @left_group_chain_complex.is_chain_complex
  -- definition rgcc_to_car [unfold 1] [coercion] := @right_group_chain_complex.car
  -- definition rgcc_to_fn  [unfold 1]            := @right_group_chain_complex.fn
  -- definition rgcc_is_chain_complex  [unfold 1] := @right_group_chain_complex.is_chain_complex

  -- -- important: these notions are shifted by one! (this is to avoid transports)
  -- definition is_exact_at_g [reducible] (X : group_chain_complex) (n : N) : Type :=
  -- Π(x : X (S n)), gcc_to_fn X n x = 1 → image (gcc_to_fn X (S n)) x
  -- definition is_exact_at_lg [reducible] (X : left_group_chain_complex) (n : N) : Type :=
  -- Π(x : X (S n)), lgcc_to_fn X n x = 1 → image (lgcc_to_fn X (S n)) x
  -- definition is_exact_at_rg [reducible] (X : right_group_chain_complex) (n : N) : Type :=
  -- Π(x : X (S n)), rgcc_to_fn X (S n) x = 1 → image (rgcc_to_fn X n) x

  -- definition is_exact_g   [reducible] (X : group_chain_complex) : Type :=
  -- Π(n : N), is_exact_at_g X n
  -- definition is_exact_lg [reducible] (X : left_group_chain_complex) : Type :=
  -- Π(n : N), is_exact_at_lg X n
  -- definition is_exact_rg [reducible] (X : right_group_chain_complex) : Type :=
  -- Π(n : N), is_exact_at_rg X n

  -- definition group_chain_complex_from_left (X : left_group_chain_complex) : group_chain_complex :=
  -- group_chain_complex.mk (int.rec X (λn, G0))
  --   begin
  --     intro n, fconstructor,
  --     { induction n with n n,
  --       { exact @lgcc_to_fn X n},
  --       { esimp, intro x, exact star}},
  --     { induction n with n n,
  --       { apply respect_mul},
  --       { intro g h, reflexivity}}
  --   end
  --   begin
  --     intro n, induction n with n n,
  --     { exact lgcc_is_chain_complex X},
  --     { esimp, intro x, reflexivity}
  --   end

  -- definition is_exact_g_from_left {X : left_group_chain_complex} {n : N} (H : is_exact_at_lg X n)
  --   : is_exact_at_g (group_chain_complex_from_left X) n :=
  -- H

  -- definition transfer_left_group_chain_complex [constructor] (X : left_group_chain_complex)
  --   {Y : N → Group} (g : Π{n : N}, Y (S n) →g Y n) (e : Π{n}, X n ≃* Y n)
  --   (p : Π{n} (x : X (S n)), e (lgcc_to_fn X n x) = g (e x)) : left_group_chain_complex :=
  -- left_group_chain_complex.mk Y @g
  --   begin
  --     intro n, apply equiv_rect (pequiv_of_equiv e), intro x,
  --     refine ap g (p x)⁻¹ ⬝ _,
  --     refine (p _)⁻¹ ⬝ _,
  --     refine ap e (lgcc_is_chain_complex X _) ⬝ _,
  --     exact respect_pt
  --   end

  -- definition is_exact_at_t_transfer {X : left_group_chain_complex} {Y : N → Type*}
  --   {g : Π{n : N}, Y (S n) →* Y n} (e : Π{n}, X n ≃* Y n)
  --   (p : Π{n} (x : X (S n)), e (lgcc_to_fn X n x) = g (e x)) {n : N}
  --   (H : is_exact_at_lg X n) : is_exact_at_lg (transfer_left_group_chain_complex X @g @e @p) n :=
  -- begin
  --   intro y q, esimp at *,
  --   have H2 : lgcc_to_fn X n (e⁻¹ᵉ* y) = pt,
  --   begin
  --     refine (inv_commute (λn, equiv_of_pequiv e) _ _ @p _)⁻¹ᵖ ⬝ _,
  --     refine ap _ q ⬝ _,
  --     exact respect_pt e⁻¹ᵉ*
  --   end,
  --   cases (H _ H2) with x r,
  --   refine image.mk (e x) _,
  --   refine (p x)⁻¹ ⬝ _,
  --   refine ap e r ⬝ _,
  --   apply right_inv
  -- end

  /-
    The following theorems state that in a chain complex, if certain types are contractible, and
    the chain complex is exact at the right spots, a map in the chain complex is an
    embedding/surjection/equivalence. For the first and third we also need to assume that
    the map is a group homomorphism (and hence that the two types around it are groups).
  -/

  definition is_embedding_of_trivial (X : chain_complex N) {n : N}
    (H : is_exact_at X n) [HX : is_contr (X (S (S n)))]
    [pgroup (X n)] [pgroup (X (S n))] [is_homomorphism (cc_to_fn X n)]
      : is_embedding (cc_to_fn X n) :=
  begin
    apply is_embedding_homomorphism,
    intro g p,
    induction H g p with x q,
    have r : pt = x, from !is_prop.elim,
    induction r,
    refine q⁻¹ ⬝ _,
    apply respect_pt
  end

  definition is_surjective_of_trivial (X : chain_complex N) {n : N}
    (H : is_exact_at X n) [HX : is_contr (X n)] : is_surjective (cc_to_fn X (S n)) :=
  begin
    intro g,
    refine trunc.elim _ (H g !is_prop.elim),
    apply tr
  end

  definition is_equiv_of_trivial (X : chain_complex N) {n : N}
    (H1 : is_exact_at X n) (H2 : is_exact_at X (S n))
    [HX1 : is_contr (X n)] [HX2 : is_contr (X (S (S (S n))))]
    [pgroup (X (S n))] [pgroup (X (S (S n)))] [is_homomorphism (cc_to_fn X (S n))]
    : is_equiv (cc_to_fn X (S n)) :=
  begin
    apply is_equiv_of_is_surjective_of_is_embedding,
    { apply is_embedding_of_trivial X, apply H2},
    { apply is_surjective_of_trivial X, apply H1},
  end

  definition is_contr_of_is_embedding_of_is_surjective {N : succ_str} (X : chain_complex N) {n : N}
    (H : is_exact_at X (S n)) [is_embedding (cc_to_fn X n)]
    [H2 : is_surjective (cc_to_fn X (S (S (S n))))] : is_contr (X (S (S n))) :=
  begin
    apply is_contr.mk pt, intro x,
    have p : cc_to_fn X n (cc_to_fn X (S n) x) = cc_to_fn X n pt,
      from !cc_is_chain_complex ⬝ !respect_pt⁻¹,
    have q : cc_to_fn X (S n) x = pt, from is_injective_of_is_embedding p,
    induction H x q with y r,
    induction H2 y with z s,
    exact (cc_is_chain_complex X _ z)⁻¹ ⬝ ap (cc_to_fn X _) s ⬝ r
  end

  end

end chain_complex
