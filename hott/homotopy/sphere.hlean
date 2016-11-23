/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the n-spheres
-/

import .susp types.trunc

open eq nat susp bool is_trunc unit pointed algebra

/-
  We can define spheres with the following possible indices:
  - trunc_index (defining S^-2 = S^-1 = empty)
  - nat (forgetting that S^-1 = empty)
  - nat, but counting wrong (S^0 = empty, S^1 = bool, ...)
  - some new type "integers >= -1"
  We choose the last option here.
-/

 /- Sphere levels -/

inductive sphere_index : Type₀ :=
| minus_one : sphere_index
| succ : sphere_index → sphere_index

notation `ℕ₋₁` := sphere_index

namespace trunc_index
  definition sub_one [reducible] (n : ℕ₋₁) : ℕ₋₂ :=
  sphere_index.rec_on n -2 (λ n k, k.+1)
  postfix `..-1`:(max+1) := sub_one

  definition of_sphere_index [reducible] (n : ℕ₋₁) : ℕ₋₂ :=
  n..-1.+1

  -- we use a double dot to distinguish with the notation .-1 in trunc_index (of type ℕ → ℕ₋₂)
end trunc_index

namespace sphere_index
  /-
     notation for sphere_index is -1, 0, 1, ...
     from 0 and up this comes from a coercion from num to sphere_index (via nat)
  -/

  postfix `.+1`:(max+1) := sphere_index.succ
  postfix `.+2`:(max+1) := λ(n : sphere_index), (n .+1 .+1)
  notation `-1` := minus_one

  definition has_zero_sphere_index [instance] : has_zero ℕ₋₁ :=
  has_zero.mk (succ minus_one)

  definition has_one_sphere_index [instance] : has_one ℕ₋₁ :=
  has_one.mk (succ (succ minus_one))

  definition add_plus_one (n m : ℕ₋₁) : ℕ₋₁ :=
  sphere_index.rec_on m n (λ k l, l .+1)

  -- addition of sphere_indices, where (-1 + -1) is defined to be -1.
  protected definition add (n m : ℕ₋₁) : ℕ₋₁ :=
  sphere_index.cases_on m
    (sphere_index.cases_on n -1 id)
    (sphere_index.rec n (λn' r, succ r))

  inductive le (a : ℕ₋₁) : ℕ₋₁ → Type :=
  | sp_refl : le a a
  | step : Π {b}, le a b → le a (b.+1)

  infix ` +1+ `:65 := sphere_index.add_plus_one

  definition has_add_sphere_index [instance] [priority 2000] [reducible] : has_add ℕ₋₁ :=
  has_add.mk sphere_index.add

  definition has_le_sphere_index [instance] : has_le ℕ₋₁ :=
  has_le.mk sphere_index.le

  definition sub_one [reducible] (n : ℕ) : ℕ₋₁ :=
  nat.rec_on n -1 (λ n k, k.+1)

  postfix `..-1`:(max+1) := sub_one

  definition of_nat [coercion] [reducible] (n : ℕ) : ℕ₋₁ :=
  n..-1.+1

  -- we use a double dot to distinguish with the notation .-1 in trunc_index (of type ℕ → ℕ₋₂)

  definition add_one [reducible] (n : ℕ₋₁) : ℕ :=
  sphere_index.rec_on n 0 (λ n k, nat.succ k)

  definition add_plus_one_of_nat (n m : ℕ) : (n +1+ m) = sphere_index.of_nat (n + m + 1) :=
  begin
    induction m with m IH,
    { reflexivity },
    { exact ap succ IH}
  end

  definition succ_sub_one (n : ℕ) : (nat.succ n)..-1 = n :> ℕ₋₁ :=
  idp

  definition add_sub_one (n m : ℕ) : (n + m)..-1 = n..-1 +1+ m..-1 :> ℕ₋₁ :=
  begin
    induction m with m IH,
    { reflexivity },
    { exact ap succ IH }
  end

  definition succ_le_succ {n m : ℕ₋₁} (H : n ≤ m) : n.+1 ≤[ℕ₋₁] m.+1 :=
  by induction H with m H IH; apply le.sp_refl; exact le.step IH

  definition minus_one_le (n : ℕ₋₁) : -1 ≤[ℕ₋₁] n :=
  by induction n with n IH; apply le.sp_refl; exact le.step IH

  open decidable
  protected definition has_decidable_eq [instance] : Π(n m : ℕ₋₁), decidable (n = m)
  | has_decidable_eq -1     -1     := inl rfl
  | has_decidable_eq (n.+1) -1     := inr (by contradiction)
  | has_decidable_eq -1     (m.+1) := inr (by contradiction)
  | has_decidable_eq (n.+1) (m.+1) :=
      match has_decidable_eq n m with
      | inl xeqy := inl (by rewrite xeqy)
      | inr xney := inr (λ h : succ n = succ m, by injection h with xeqy; exact absurd xeqy xney)
      end

  definition not_succ_le_minus_two {n : sphere_index} (H : n .+1 ≤[ℕ₋₁] -1) : empty :=
  by cases H

  protected definition le_trans {n m k : ℕ₋₁} (H1 : n ≤[ℕ₋₁] m) (H2 : m ≤[ℕ₋₁] k) : n ≤[ℕ₋₁] k :=
  begin
    induction H2 with k H2 IH,
    { exact H1},
    { exact le.step IH}
  end

  definition le_of_succ_le_succ {n m : ℕ₋₁} (H : n.+1 ≤[ℕ₋₁] m.+1) : n ≤[ℕ₋₁] m :=
  begin
    cases H with m H',
    { apply le.sp_refl},
    { exact sphere_index.le_trans (le.step !le.sp_refl) H'}
  end

  theorem not_succ_le_self {n : ℕ₋₁} : ¬n.+1 ≤[ℕ₋₁] n :=
  begin
    induction n with n IH: intro H,
    { exact not_succ_le_minus_two H},
    { exact IH (le_of_succ_le_succ H)}
  end

  protected definition le_antisymm {n m : ℕ₋₁} (H1 : n ≤[ℕ₋₁] m) (H2 : m ≤[ℕ₋₁] n) : n = m :=
  begin
    induction H2 with n H2 IH,
    { reflexivity},
    { exfalso, apply @not_succ_le_self n, exact sphere_index.le_trans H1 H2}
  end

  protected definition le_succ {n m : ℕ₋₁} (H1 : n ≤[ℕ₋₁] m): n ≤[ℕ₋₁] m.+1 :=
  le.step H1

  definition add_plus_one_minus_one (n : ℕ₋₁) : n +1+ -1 = n := idp
  definition add_plus_one_succ (n m : ℕ₋₁) : n +1+ (m.+1) = (n +1+ m).+1 := idp
  definition minus_one_add_plus_one (n : ℕ₋₁) : -1 +1+ n = n :=
  begin induction n with n IH, reflexivity, exact ap succ IH end
  definition succ_add_plus_one (n m : ℕ₋₁) : (n.+1) +1+ m = (n +1+ m).+1 :=
  begin induction m with m IH, reflexivity, exact ap succ IH end

  definition sphere_index_of_nat_add_one (n : ℕ₋₁) : sphere_index.of_nat (add_one n) = n.+1 :=
  begin induction n with n IH, reflexivity, exact ap succ IH end

  definition add_one_succ (n : ℕ₋₁) : add_one (n.+1) = succ (add_one n) :=
  by reflexivity

  definition add_one_sub_one (n : ℕ) : add_one (n..-1) = n :=
  begin induction n with n IH, reflexivity, exact ap nat.succ IH end

  definition add_one_of_nat (n : ℕ) : add_one n = nat.succ n :=
  ap nat.succ (add_one_sub_one n)

  definition sphere_index.of_nat_succ (n : ℕ)
    : sphere_index.of_nat (nat.succ n) = (sphere_index.of_nat n).+1 :=
  begin induction n with n IH, reflexivity, exact ap succ IH end

  /-
    warning: if this coercion is available, the coercion ℕ → ℕ₋₂ is the composition of the coercions
    ℕ → ℕ₋₁ → ℕ₋₂. We don't want this composition as coercion, because it has worse computational
    properties. You can rewrite it with trans_to_of_sphere_index_eq defined below.
  -/
  attribute trunc_index.of_sphere_index [coercion]

end sphere_index open sphere_index

definition weak_order_sphere_index [trans_instance] [reducible] : weak_order sphere_index :=
weak_order.mk le sphere_index.le.sp_refl @sphere_index.le_trans @sphere_index.le_antisymm

namespace trunc_index
  definition sub_two_eq_sub_one_sub_one (n : ℕ) : n.-2 = n..-1..-1 :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap trunc_index.succ IH}
  end

  definition of_nat_sub_one (n : ℕ)
    : (sphere_index.of_nat n)..-1 = (trunc_index.sub_two n).+1 :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap trunc_index.succ IH}
  end

  definition sub_one_of_sphere_index (n : ℕ)
    : of_sphere_index n..-1 = (trunc_index.sub_two n).+1 :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap trunc_index.succ IH}
  end

  definition succ_sub_one (n : ℕ₋₁) : n.+1..-1 = n :> ℕ₋₂ :=
  idp

  definition of_sphere_index_of_nat (n : ℕ)
    : of_sphere_index (sphere_index.of_nat n) = of_nat n :> ℕ₋₂ :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap trunc_index.succ IH}
  end

  definition trans_to_of_sphere_index_eq (n : ℕ)
    : trunc_index._trans_to_of_sphere_index n = of_nat n :> ℕ₋₂ :=
  of_sphere_index_of_nat n

  definition trunc_index_of_nat_add_one (n : ℕ₋₁)
    : trunc_index.of_nat (add_one n) = (of_sphere_index n).+1 :=
  begin induction n with n IH, reflexivity, exact ap succ IH end

  definition of_sphere_index_succ (n : ℕ₋₁) : of_sphere_index (n.+1) = (of_sphere_index n).+1 :=
  begin induction n with n IH, reflexivity, exact ap succ IH end

end trunc_index

open sphere_index equiv

definition sphere (n : ℕ₋₁) : Type₀ := iterate_susp (add_one n) empty

namespace sphere

  export [notation] sphere_index

  definition base {n : ℕ} : sphere n := north
  definition pointed_sphere [instance] [constructor] (n : ℕ) : pointed (sphere n) :=
  pointed.mk base
  definition psphere [constructor] (n : ℕ) : Type* := pointed.mk' (sphere n)


  namespace ops
    abbreviation S := sphere
    notation `S*` := psphere
  end ops
  open sphere.ops

  definition sphere_minus_one : S -1 = empty := idp
  definition sphere_succ [unfold_full] (n : ℕ₋₁) : S n.+1 = susp (S n) := idp
  definition psphere_succ [unfold_full] (n : ℕ) : S* (n + 1) = psusp (S* n) := idp
  definition psphere_eq_iterate_susp (n : ℕ)
    : S* n = pointed.MK (iterate_susp (succ n) empty) !north :=
  begin
    esimp,
    apply ap (λx, pointed.MK (susp x) (@north x)); apply ap (λx, iterate_susp x empty),
    apply add_one_sub_one
  end

  definition equator [constructor] (n : ℕ) : S* n →* Ω (S* (succ n)) :=
  loop_psusp_unit (S* n)

  definition surf {n : ℕ} : Ω[n] (S* n) :=
  begin
    induction n with n s,
    { exact south },
    { exact (loopn_succ_in (S* (succ n)) n)⁻¹ᵉ* (apn n (equator n) s), }
  end

  definition bool_of_sphere [unfold 1] : S 0 → bool :=
  proof susp.rec ff tt (λx, empty.elim x) qed

  definition sphere_of_bool [unfold 1] : bool → S 0
  | ff := proof north qed
  | tt := proof south qed

  definition sphere_equiv_bool [constructor] : S 0 ≃ bool :=
  equiv.MK bool_of_sphere
           sphere_of_bool
           (λb, match b with | tt := idp | ff := idp end)
           (λx, proof susp.rec_on x idp idp (empty.rec _) qed)

  definition psphere_pequiv_pbool [constructor] : S* 0 ≃* pbool :=
  pequiv_of_equiv sphere_equiv_bool idp

  definition sphere_eq_bool : S 0 = bool :=
  ua sphere_equiv_bool

  definition sphere_eq_pbool : S* 0 = pbool :=
  pType_eq sphere_equiv_bool idp

  definition psphere_pmap_pequiv' (A : Type*) (n : ℕ) : ppmap (S* n) A ≃* Ω[n] A :=
  begin
    revert A, induction n with n IH: intro A,
    { refine _ ⬝e* !pmap_pbool_pequiv, exact pequiv_ppcompose_right psphere_pequiv_pbool⁻¹ᵉ* },
    { refine psusp_adjoint_loop (S* n) A ⬝e* IH (Ω A) ⬝e* !loopn_succ_in⁻¹ᵉ*  }
  end

  definition psphere_pmap_pequiv (A : Type*) (n : ℕ) : ppmap (S* n) A ≃* Ω[n] A :=
  begin
    fapply pequiv_change_fun,
    { exact psphere_pmap_pequiv' A n },
    { exact papn_fun A surf },
    { revert A, induction n with n IH: intro A,
      { reflexivity },
      { intro f, refine ap !loopn_succ_in⁻¹ᵉ* (IH (Ω A) _ ⬝ !apn_pcompose _) ⬝ _,
        exact !loopn_succ_in_inv_natural⁻¹* _ }}
  end

  protected definition elim {n : ℕ} {P : Type*} (p : Ω[n] P) : S* n →* P :=
  !psphere_pmap_pequiv⁻¹ᵉ* p

  -- definition elim_surf {n : ℕ} {P : Type*} (p : Ω[n] P) : apn n (sphere.elim p) surf = p :=
  -- begin
  --   induction n with n IH,
  --   { esimp [apn,surf,sphere.elim,psphere_pmap_equiv], apply sorry},
  --   { apply sorry}
  -- end

end sphere

namespace sphere
  open is_conn trunc_index sphere_index sphere.ops

  -- Corollary 8.2.2
  theorem is_conn_sphere [instance] (n : ℕ₋₁) : is_conn (n..-1) (S n) :=
  begin
    induction n with n IH,
    { apply is_conn_minus_two },
    { rewrite [trunc_index.succ_sub_one n, sphere.sphere_succ],
      apply is_conn_susp }
  end

  theorem is_conn_psphere [instance] (n : ℕ) : is_conn (n.-1) (S* n) :=
  transport (λx, is_conn x (sphere n)) (of_nat_sub_one n) (is_conn_sphere n)

end sphere

open sphere sphere.ops

namespace is_trunc
  open trunc_index
  variables {n : ℕ} {A : Type}
  definition is_trunc_of_psphere_pmap_equiv_constant
    (H : Π(a : A) (f : S* n →* pointed.Mk a) (x : S n), f x = f base) : is_trunc (n.-2.+1) A :=
  begin
    apply iff.elim_right !is_trunc_iff_is_contr_loop,
    intro a,
    apply is_trunc_equiv_closed, exact !psphere_pmap_pequiv,
    fapply is_contr.mk,
    { exact pmap.mk (λx, a) idp},
    { intro f, fapply pmap_eq,
      { intro x, esimp, refine !respect_pt⁻¹ ⬝ (!H ⬝ !H⁻¹)},
      { rewrite [▸*,con.right_inv,▸*,con.left_inv]}}
  end

  definition is_trunc_iff_map_sphere_constant
    (H : Π(f : S n → A) (x : S n), f x = f base) : is_trunc (n.-2.+1) A :=
  begin
    apply is_trunc_of_psphere_pmap_equiv_constant,
    intros, cases f with f p, esimp at *, apply H
  end

  definition psphere_pmap_equiv_constant_of_is_trunc' [H : is_trunc (n.-2.+1) A]
    (a : A) (f : S* n →* pointed.Mk a) (x : S n) : f x = f base :=
  begin
    let H' := iff.elim_left (is_trunc_iff_is_contr_loop n A) H a,
    note H'' := @is_trunc_equiv_closed_rev _ _ _ !psphere_pmap_pequiv H',
    esimp at H'',
    have p : f = pmap.mk (λx, f base) (respect_pt f),
      by apply is_prop.elim,
    exact ap10 (ap pmap.to_fun p) x
  end

  definition psphere_pmap_equiv_constant_of_is_trunc [H : is_trunc (n.-2.+1) A]
    (a : A) (f : S* n →* pointed.Mk a) (x y : S n) : f x = f y :=
  let H := psphere_pmap_equiv_constant_of_is_trunc' a f in !H ⬝ !H⁻¹

  definition map_sphere_constant_of_is_trunc [H : is_trunc (n.-2.+1) A]
    (f : S n → A) (x y : S n) : f x = f y :=
  psphere_pmap_equiv_constant_of_is_trunc (f base) (pmap.mk f idp) x y

  definition map_sphere_constant_of_is_trunc_self [H : is_trunc (n.-2.+1) A]
    (f : S n → A) (x : S n) : map_sphere_constant_of_is_trunc f x x = idp :=
  !con.right_inv

end is_trunc
