/-
Copyright (c) 2016 Ulrik Buchholtz and Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke

H-spaces and the Hopf construction
-/

import types.equiv .wedge .join

open eq eq.ops equiv is_equiv is_conn is_trunc trunc susp join

namespace hopf

structure h_space [class] (A : Type) extends has_mul A, has_one A :=
(one_mul : ∀a, mul one a = a) (mul_one : ∀a, mul a one = a)

section
  variable {A : Type}
  variable [H : h_space A]
  include H

  definition one_mul (a : A) : 1 * a = a := !h_space.one_mul
  definition mul_one (a : A) : a * 1 = a := !h_space.mul_one

  definition h_space_equiv_closed {B : Type} (f : A ≃ B) : h_space B :=
  ⦃ h_space, one := f 1, mul := (λb b', f (f⁻¹ b * f⁻¹ b')),
    one_mul := by intro b; rewrite [to_left_inv,one_mul,to_right_inv],
    mul_one := by intro b; rewrite [to_left_inv,mul_one,to_right_inv] ⦄

  /- Lemma 8.5.5.
     If A is 0-connected, then left and right multiplication are equivalences -/
  variable [K : is_conn 0 A]
  include K

  definition is_equiv_mul_left [instance] : Π(a : A), is_equiv (λx, a * x) :=
  begin
    apply is_conn_map.elim (is_conn_map_from_unit -1 A 1)
                           (λa, trunctype.mk' -1 (is_equiv (λx, a * x))),
    intro z, change is_equiv (λx : A, 1 * x), apply is_equiv.homotopy_closed id,
    intro x, apply inverse, apply one_mul
  end

  definition is_equiv_mul_right [instance]  : Π(a : A), is_equiv (λx, x * a) :=
  begin
    apply is_conn_map.elim (is_conn_map_from_unit -1 A 1)
                           (λa, trunctype.mk' -1 (is_equiv (λx, x * a))),
    intro z, change is_equiv (λx : A, x * 1), apply is_equiv.homotopy_closed id,
    intro x, apply inverse, apply mul_one
  end
end

section
  variable (A : Type)
  variables [H : h_space A] [K : is_conn 0 A]
  include H K

  definition hopf : susp A → Type :=
  susp.elim_type A A (λa, equiv.mk (λx, a * x) !is_equiv_mul_left)

  /- Lemma 8.5.7. The total space is A * A -/
  open prod prod.ops

  protected definition total : sigma (hopf A) ≃ join A A :=
  begin
    apply equiv.trans (susp.flattening A A A _), unfold join,
    apply equiv.trans (pushout.symm pr₂ (λz : A × A, z.1 * z.2)),
    fapply pushout.equiv,
    { fapply equiv.MK
             (λz : A × A, (z.1 * z.2, z.2))
             (λz : A × A, ((λx, x * z.2)⁻¹ z.1, z.2)),
      { intro z, induction z with u v, esimp, 
        exact prod_eq (right_inv (λx, x * v) u) idp },
      { intro z, induction z with a b, esimp,
        exact prod_eq (left_inv (λx, x * b) a) idp } },
    { exact erfl },
    { exact erfl },
    { intro z, reflexivity },
    { intro z, reflexivity }
  end
end

/- If A is a K(G,1), then A is deloopable.
   Main lemma of Licata-Finster. -/
section
  parameters (A : Type) [T : is_trunc 1 A] [K : is_conn 0 A] [H : h_space A]
             (coh : one_mul 1 = mul_one 1 :> (1 * 1 = 1 :> A))
  definition P [reducible] : susp A → Type :=
  λx, trunc 1 (north = x)

  include K H T

  local abbreviation codes [reducible] : susp A → Type := hopf A

  definition transport_codes_merid (a a' : A)
    : transport codes (merid a) a' = a * a' :> A :=
  by krewrite elim_type_merid

  definition is_trunc_codes [instance] (x : susp A) : is_trunc 1 (codes x) :=
  begin
    induction x with a, do 2 apply T, apply is_prop.elimo
  end

  definition encode₀ {x : susp A} : north = x → codes x :=
  λp, transport codes p (by change A; exact 1)

  definition encode {x : susp A} : P x → codes x :=
  λp, trunc.elim encode₀ p

  definition decode' : A → P (@north A) :=
  λa, tr (merid a ⬝ (merid 1)⁻¹)

  definition transport_codes_merid_one_inv (a : A)
    : transport codes (merid 1)⁻¹ a = a :=
  begin
    rewrite tr_inv,
    apply @inv_eq_of_eq A A (transport codes (merid 1)) _ a a,
    krewrite elim_type_merid,
    change a = 1 * a,
    rewrite one_mul
  end

  proposition encode_decode' (a : A) : encode (decode' a) = a :=
  begin
    unfold decode', unfold encode, unfold encode₀,
    rewrite [con_tr,transport_codes_merid,mul_one,tr_inv],
    apply transport_codes_merid_one_inv
  end

  include coh

  open pointed
  proposition homomorphism : Πa a' : A,
    tr (merid (a * a')) = tr (merid a' ⬝ (merid 1)⁻¹ ⬝ merid a)
      :> trunc 1 (@north A = @south A) :=
  begin
    fapply @wedge_extension.ext (pointed.MK A 1) (pointed.MK A 1) 0 0
      K K (λa a' : A, trunctype.mk' 0
        (tr (merid (a * a')) = tr (merid a' ⬝ (merid 1)⁻¹ ⬝ merid a))),
    { change Πa : A,
             tr (merid (a * 1)) = tr (merid 1 ⬝ (merid 1)⁻¹ ⬝ merid a)
             :> trunc 1 (@north A = @south A),
      intro a, apply ap tr,
      exact calc
        merid (a * 1) = merid a : ap merid (mul_one a)
                  ... = merid 1 ⬝ (merid 1)⁻¹ ⬝ merid a
        : (idp_con (merid a))⁻¹
          ⬝ ap (λw, w ⬝ merid a) (con.right_inv (merid 1))⁻¹ },
    { change Πa' : A,
             tr (merid (1 * a')) = tr (merid a' ⬝ (merid 1)⁻¹ ⬝ merid 1)
             :> trunc 1 (@north A = @south A),
      intro a', apply ap tr,
      exact calc
        merid (1 * a') = merid a' : ap merid (one_mul a')
                   ... = merid a' ⬝ (merid 1)⁻¹ ⬝ merid 1
        : ap (λw, merid a' ⬝ w) (con.left_inv (merid 1))⁻¹
        ⬝ (con.assoc' (merid a') (merid 1)⁻¹ (merid 1)) },
    { apply ap02 tr, esimp, fapply concat2,
      { apply ap02 merid, exact coh⁻¹ },
      { assert e : Π(X : Type)(x y : X)(p : x = y),
               (idp_con p)⁻¹ ⬝ ap (λw : x = x, w ⬝ p) (con.right_inv p)⁻¹
               = ap (concat p) (con.left_inv p)⁻¹ ⬝ con.assoc' p p⁻¹ p,
        { intros X x y p, cases p, reflexivity },
        apply e } }
  end

  definition decode {x : susp A} : codes x → P x :=
  begin
    induction x,
    { exact decode' },
    { exact (λa, tr (merid a)) },
    { apply pi.arrow_pathover_left, esimp, intro a',
      apply pathover_of_tr_eq, krewrite susp.elim_type_merid, esimp,
      krewrite [trunc_transport,transport_eq_r], apply inverse,
      apply homomorphism }
  end

  proposition decode_encode {x : susp A} : Πt : P x, decode (encode t) = t :=
  begin
    apply trunc.rec, intro p, cases p, apply ap tr, apply con.right_inv
  end

  definition main_lemma : trunc 1 (north = north :> susp A) ≃ A :=
  equiv.MK encode decode' encode_decode' decode_encode

  definition main_lemma_point
    : pointed.MK (trunc 1 (Ω(psusp A))) (tr idp) ≃* pointed.MK A 1 :=
  pointed.pequiv_of_equiv main_lemma idp

  protected definition delooping : (tr north = tr north :> trunc 2 (susp A)) ≃ A :=
  (tr_eq_tr_equiv 1 north north) ⬝e main_lemma

end

end hopf
