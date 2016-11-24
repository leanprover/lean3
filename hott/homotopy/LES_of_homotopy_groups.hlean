/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

We define the fiber sequence of a pointed map f : X →* Y. We mostly follow the proof in section 8.4
of the book.

PART 1:
We define a sequence fiber_sequence as in Definition 8.4.3.
It has types X(n) : Type*
X(0)   := Y,
X(1)   := X,
X(n+1) := fiber (f(n))
with functions f(n) : X(n+1) →* X(n)
f(0)   := f
f(n+1) := point (f(n)) [this is the first projection]
We prove that this is an exact sequence.
Then we prove Lemma 8.4.3, by showing that X(n+3) ≃* Ω(X(n)) and that this equivalence sends
the pointed map f(n+3) to -Ω(f(n)), i.e. the composition of Ω(f(n)) with path inversion.
Using this equivalence we get a boundary_map : Ω(Y) → pfiber f.

PART 2:
Now we can define a new fiber sequence X'(n) : Type*, and here we slightly diverge from the book.
We define it as
X'(0)   := Y,
X'(1)   := X,
X'(2)   := fiber f
X'(n+3) := Ω(X'(n))
with maps f'(n) : X'(n+1) →* X'(n)
f'(0) := f
f'(1) := point f
f'(2) := boundary_map
f'(n+3) := Ω(f'(n))

This sequence is not equivalent to the previous sequence. The difference is in the signs.
The sequence f has negative signs (i.e. is composed with the inverse maps) for n ≡ 3, 4, 5 mod 6.
This sign information is captured by e : X'(n) ≃* X'(n) such that
e(k)   := 1               for k = 0,1,2,3
e(k+3) := Ω(e(k)) ∘ (-)⁻¹ for k > 0

Now the sequence (X', f' ∘ e) is equivalent to (X, f), Hence (X', f' ∘ e) is an exact sequence.
We then prove that (X', f') is an exact sequence by using that there are other equivalences
eₗ and eᵣ such that
f' = eᵣ ∘ f' ∘ e
f' ∘ eₗ = e ∘ f'.
(this fact is type_chain_complex_cancel_aut and is_exact_at_t_cancel_aut in the file chain_complex)
eₗ and eᵣ are almost the same as e, except that the places where the inverse is taken is
slightly shifted:
eᵣ = (-)⁻¹ for n ≡ 3, 4, 5 mod 6                       and eᵣ = 1 otherwise
e  = (-)⁻¹ for n ≡ 4, 5, 6 mod 6 (except for n = 0)    and e  = 1 otherwise
eₗ = (-)⁻¹ for n ≡ 5, 6, 7 mod 6 (except for n = 0, 1) and eₗ = 1 otherwise

PART 3:
We change the type over which the sequence of types and maps are indexed from ℕ to ℕ × 3
(where 3 is the finite type with 3 elements). The reason is that we have that X'(3n) = Ωⁿ(Y), but
this equality is not definitionally true. Hence we cannot even state whether f'(3n) = Ωⁿ(f) without
using transports. This gets ugly. However, if we use as index type ℕ × 3, we can do this. We can
define
Y : ℕ × 3 → Type* as
Y(n, 0) := Ωⁿ(Y)
Y(n, 1) := Ωⁿ(X)
Y(n, 2) := Ωⁿ(fiber f)
with maps g(n) : Y(S n) →* Y(n) (where the successor is defined in the obvious way)
g(n, 0) := Ωⁿ(f)
g(n, 1) := Ωⁿ(point f)
g(n, 2) := Ωⁿ(boundary_map) ∘ cast

Here "cast" is the transport over the equality Ωⁿ⁺¹(Y) = Ωⁿ(Ω(Y)). We show that the sequence
(ℕ, X', f') is equivalent to (ℕ × 3, Y, g).

PART 4:
We get the long exact sequence of homotopy groups by taking the set-truncation of (Y, g).
-/

import .chain_complex algebra.homotopy_group eq2

open eq pointed sigma fiber equiv is_equiv sigma.ops is_trunc nat trunc algebra function sum
/--------------
    PART 1
 --------------/

namespace chain_complex

  definition fiber_sequence_helper [constructor] (v : Σ(X Y : Type*), X →* Y)
    : Σ(Z X : Type*), Z →* X :=
  ⟨pfiber v.2.2, v.1, ppoint v.2.2⟩

  definition fiber_sequence_helpern (v : Σ(X Y : Type*), X →* Y) (n : ℕ)
    : Σ(Z X : Type*), Z →* X :=
  iterate fiber_sequence_helper n v

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X →* Y)
  include f

  definition fiber_sequence_carrier (n : ℕ) : Type* :=
  (fiber_sequence_helpern ⟨X, Y, f⟩ n).2.1

  definition fiber_sequence_fun (n : ℕ)
    : fiber_sequence_carrier (n + 1) →* fiber_sequence_carrier n :=
  (fiber_sequence_helpern ⟨X, Y, f⟩ n).2.2

  /- Definition 8.4.3 -/
  definition fiber_sequence : type_chain_complex.{0 u} +ℕ :=
  begin
    fconstructor,
    { exact fiber_sequence_carrier},
    { exact fiber_sequence_fun},
    { intro n x, cases n with n,
      { exact point_eq x},
      { exact point_eq x}}
  end

  definition is_exact_fiber_sequence : is_exact_t fiber_sequence :=
  λn x p, fiber.mk (fiber.mk x p) rfl

  /- (generalization of) Lemma 8.4.4(i)(ii) -/
  definition fiber_sequence_carrier_equiv (n : ℕ)
    : fiber_sequence_carrier (n+3) ≃ Ω(fiber_sequence_carrier n) :=
  calc
    fiber_sequence_carrier (n+3) ≃ fiber (fiber_sequence_fun (n+1)) pt : erfl
    ... ≃ Σ(x : fiber_sequence_carrier _), fiber_sequence_fun (n+1) x = pt
      : fiber.sigma_char
    ... ≃ Σ(x : fiber (fiber_sequence_fun n) pt), fiber_sequence_fun _ x = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier _), fiber_sequence_fun _ x = pt),
            fiber_sequence_fun _ (fiber.mk v.1 v.2) = pt
      : by exact sigma_equiv_sigma !fiber.sigma_char (λa, erfl)
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier _), fiber_sequence_fun _ x = pt),
            v.1 = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier _), x = pt),
            fiber_sequence_fun _ v.1 = pt
      : sigma_assoc_comm_equiv
    ... ≃ fiber_sequence_fun _ !center.1 = pt
      : @(sigma_equiv_of_is_contr_left _) !is_contr_sigma_eq'
    ... ≃ fiber_sequence_fun _ pt = pt
      : erfl
    ... ≃ pt = pt
      : by exact !equiv_eq_closed_left !respect_pt
    ... ≃ Ω(fiber_sequence_carrier n) : erfl

  /- computation rule -/
  definition fiber_sequence_carrier_equiv_eq (n : ℕ)
    (x : fiber_sequence_carrier (n+1)) (p : fiber_sequence_fun n x = pt)
    (q : fiber_sequence_fun (n+1) (fiber.mk x p) = pt)
    : fiber_sequence_carrier_equiv n (fiber.mk (fiber.mk x p) q)
      = !respect_pt⁻¹ ⬝ ap (fiber_sequence_fun n) q⁻¹ ⬝ p :=
  begin
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    refine eq_transport_Fl _ _ ⬝ _,
    apply whisker_right,
    refine inverse2 !ap_inv ⬝ !inv_inv ⬝ _,
    refine ap_compose (fiber_sequence_fun n) pr₁ _ ⬝
           ap02 (fiber_sequence_fun n) !ap_pr1_center_eq_sigma_eq',
  end

  definition fiber_sequence_carrier_equiv_inv_eq (n : ℕ)
    (p : Ω(fiber_sequence_carrier n)) : (fiber_sequence_carrier_equiv n)⁻¹ᵉ p =
      fiber.mk (fiber.mk pt (respect_pt (fiber_sequence_fun n) ⬝ p)) idp :=
  begin
    apply inv_eq_of_eq,
    refine _ ⬝ !fiber_sequence_carrier_equiv_eq⁻¹, esimp,
    exact !inv_con_cancel_left⁻¹
  end

  definition fiber_sequence_carrier_pequiv (n : ℕ)
    : fiber_sequence_carrier (n+3) ≃* Ω(fiber_sequence_carrier n) :=
  pequiv_of_equiv (fiber_sequence_carrier_equiv n)
    begin
      esimp,
      apply con.left_inv
    end

  definition fiber_sequence_carrier_pequiv_eq (n : ℕ)
    (x : fiber_sequence_carrier (n+1)) (p : fiber_sequence_fun n x = pt)
    (q : fiber_sequence_fun (n+1) (fiber.mk x p) = pt)
    : fiber_sequence_carrier_pequiv n (fiber.mk (fiber.mk x p) q)
      = !respect_pt⁻¹ ⬝ ap (fiber_sequence_fun n) q⁻¹ ⬝ p :=
  fiber_sequence_carrier_equiv_eq n x p q

  definition fiber_sequence_carrier_pequiv_inv_eq (n : ℕ)
    (p : Ω(fiber_sequence_carrier n)) : (fiber_sequence_carrier_pequiv n)⁻¹ᵉ* p =
      fiber.mk (fiber.mk pt (respect_pt (fiber_sequence_fun n) ⬝ p)) idp :=
  by rexact fiber_sequence_carrier_equiv_inv_eq n p

  /- Lemma 8.4.4(iii) -/
  definition fiber_sequence_fun_eq_helper (n : ℕ)
    (p : Ω(fiber_sequence_carrier (n + 1))) :
    fiber_sequence_carrier_pequiv n
      (fiber_sequence_fun (n + 3)
        ((fiber_sequence_carrier_pequiv (n + 1))⁻¹ᵉ* p)) =
          ap1 (fiber_sequence_fun n) p⁻¹ :=
  begin
    refine ap (λx, fiber_sequence_carrier_pequiv n (fiber_sequence_fun (n + 3) x))
              (fiber_sequence_carrier_pequiv_inv_eq (n+1) p) ⬝ _,
    /- the following three lines are rewriting some reflexivities: -/
    -- replace (n + 3) with (n + 2 + 1),
    -- refine ap (fiber_sequence_carrier_pequiv n)
    --           (fiber_sequence_fun_eq1 (n+2) _ idp) ⬝ _,
    refine fiber_sequence_carrier_pequiv_eq n pt (respect_pt (fiber_sequence_fun n)) _ ⬝ _,
    esimp,
    apply whisker_right,
    apply whisker_left,
    apply ap02, apply inverse2, apply idp_con,
  end

  theorem fiber_sequence_carrier_pequiv_eq_point_eq_idp (n : ℕ) :
    fiber_sequence_carrier_pequiv_eq n
      (Point (fiber_sequence_carrier (n+1)))
      (respect_pt (fiber_sequence_fun n))
      (respect_pt (fiber_sequence_fun (n + 1))) = idp :=
  begin
    apply con_inv_eq_idp,
    refine ap (λx, whisker_left _ (_ ⬝ x)) _ ⬝ _,
    { reflexivity},
    { reflexivity},
    refine ap (whisker_left _)
              (eq_transport_Fl_idp_left (fiber_sequence_fun n)
                                        (respect_pt (fiber_sequence_fun n))) ⬝ _,
    apply whisker_left_idp_con_eq_assoc
  end

  theorem fiber_sequence_fun_phomotopy_helper (n : ℕ) :
    (fiber_sequence_carrier_pequiv n ∘*
      fiber_sequence_fun (n + 3)) ∘*
        (fiber_sequence_carrier_pequiv (n + 1))⁻¹ᵉ* ~*
          ap1 (fiber_sequence_fun n) ∘* pinverse :=
  begin
    fapply phomotopy.mk,
    { exact chain_complex.fiber_sequence_fun_eq_helper f n},
    { esimp, rewrite [idp_con], refine _ ⬝ whisker_left _ !idp_con⁻¹,
      apply whisker_right,
      apply whisker_left,
      exact chain_complex.fiber_sequence_carrier_pequiv_eq_point_eq_idp f n}
  end

  theorem fiber_sequence_fun_eq (n : ℕ) : Π(x : fiber_sequence_carrier (n + 4)),
    fiber_sequence_carrier_pequiv n (fiber_sequence_fun (n + 3) x) =
      ap1 (fiber_sequence_fun n) (fiber_sequence_carrier_pequiv (n + 1) x)⁻¹ :=
  begin
    apply homotopy_of_inv_homotopy_pre (fiber_sequence_carrier_pequiv (n + 1)),
    apply fiber_sequence_fun_eq_helper n
  end

  theorem fiber_sequence_fun_phomotopy (n : ℕ) :
    fiber_sequence_carrier_pequiv n ∘*
      fiber_sequence_fun (n + 3) ~*
          (ap1 (fiber_sequence_fun n) ∘* pinverse) ∘* fiber_sequence_carrier_pequiv (n + 1) :=
  begin
    apply phomotopy_of_pinv_right_phomotopy,
    apply fiber_sequence_fun_phomotopy_helper
  end

  definition boundary_map : Ω Y →* pfiber f :=
  fiber_sequence_fun 2 ∘* (fiber_sequence_carrier_pequiv 0)⁻¹ᵉ*

/--------------
    PART 2
 --------------/

  /- Now we are ready to define the long exact sequence of homotopy groups.
     First we define its carrier -/
  definition loop_spaces : ℕ → Type*
  | 0     := Y
  | 1     := X
  | 2     := pfiber f
  | (k+3) := Ω (loop_spaces k)

  /- The maps between the homotopy groups -/
  definition loop_spaces_fun
    : Π(n : ℕ), loop_spaces (n+1) →* loop_spaces n
  | 0     := proof f qed
  | 1     := proof ppoint f qed
  | 2     := proof boundary_map qed
  | (k+3) := proof ap1 (loop_spaces_fun k) qed

  definition loop_spaces_fun_add3 [unfold_full] (n : ℕ) :
    loop_spaces_fun (n + 3) = ap1 (loop_spaces_fun n) :=
  proof idp qed

  definition fiber_sequence_pequiv_loop_spaces :
    Πn, fiber_sequence_carrier n ≃* loop_spaces n
  | 0     := by reflexivity
  | 1     := by reflexivity
  | 2     := by reflexivity
  | (k+3) :=
    begin
      refine fiber_sequence_carrier_pequiv k ⬝e* _,
      apply loop_pequiv_loop,
      exact fiber_sequence_pequiv_loop_spaces k
    end

  definition fiber_sequence_pequiv_loop_spaces_add3 (n : ℕ)
    : fiber_sequence_pequiv_loop_spaces (n + 3) =
      ap1 (fiber_sequence_pequiv_loop_spaces n) ∘* fiber_sequence_carrier_pequiv n :=
  by reflexivity

  definition fiber_sequence_pequiv_loop_spaces_3_phomotopy
    : fiber_sequence_pequiv_loop_spaces 3 ~* proof fiber_sequence_carrier_pequiv nat.zero qed :=
  begin
    refine pwhisker_right _ ap1_pid ⬝* _,
    apply pid_pcompose
  end

  definition pid_or_pinverse : Π(n : ℕ), loop_spaces n ≃* loop_spaces n
  | 0     := pequiv.rfl
  | 1     := pequiv.rfl
  | 2     := pequiv.rfl
  | 3     := pequiv.rfl
  | (k+4) := !pequiv_pinverse ⬝e* loop_pequiv_loop (pid_or_pinverse (k+1))

  definition pid_or_pinverse_add4 (n : ℕ)
    : pid_or_pinverse (n + 4) = !pequiv_pinverse ⬝e* loop_pequiv_loop (pid_or_pinverse (n + 1)) :=
  by reflexivity

  definition pid_or_pinverse_add4_rev : Π(n : ℕ),
    pid_or_pinverse (n + 4) ~* pinverse ∘* Ω→(pid_or_pinverse (n + 1))
  | 0     := begin rewrite [pid_or_pinverse_add4, + to_pmap_pequiv_trans],
                   replace pid_or_pinverse (0 + 1) with pequiv.refl X,
                   refine pwhisker_right _ !loop_pequiv_loop_rfl ⬝* _, refine !pid_pcompose ⬝* _,
                   exact !pcompose_pid⁻¹* ⬝* pwhisker_left _ !ap1_pid⁻¹* end
  | 1     := begin rewrite [pid_or_pinverse_add4, + to_pmap_pequiv_trans],
                   replace pid_or_pinverse (1 + 1) with pequiv.refl (pfiber f),
                   refine pwhisker_right _ !loop_pequiv_loop_rfl ⬝* _, refine !pid_pcompose ⬝* _,
                   exact !pcompose_pid⁻¹* ⬝* pwhisker_left _ !ap1_pid⁻¹* end
  | 2     := begin rewrite [pid_or_pinverse_add4, + to_pmap_pequiv_trans],
                   replace pid_or_pinverse (2 + 1) with pequiv.refl (Ω Y),
                   refine pwhisker_right _ !loop_pequiv_loop_rfl ⬝* _, refine !pid_pcompose ⬝* _,
                   exact !pcompose_pid⁻¹* ⬝* pwhisker_left _ !ap1_pid⁻¹* end
  | (k+3) :=
    begin
      replace (k + 3 + 1) with (k + 4),
      rewrite [+ pid_or_pinverse_add4, + to_pmap_pequiv_trans],
      refine _ ⬝* pwhisker_left _ !ap1_pcompose⁻¹*,
      refine _ ⬝* !passoc,
      apply pconcat2,
      { refine ap1_phomotopy (pid_or_pinverse_add4_rev k) ⬝* _,
        refine !ap1_pcompose ⬝* _, apply pwhisker_right, apply ap1_pinverse},
      { refine !ap1_pinverse⁻¹*}
    end

  theorem fiber_sequence_phomotopy_loop_spaces : Π(n : ℕ),
    fiber_sequence_pequiv_loop_spaces n ∘* fiber_sequence_fun n ~*
      (loop_spaces_fun n ∘* pid_or_pinverse (n + 1)) ∘* fiber_sequence_pequiv_loop_spaces (n + 1)
  | 0     := proof proof phomotopy.rfl qed ⬝* pwhisker_right _ !pcompose_pid⁻¹* qed
  | 1     := by reflexivity
  | 2     :=
    begin
      refine !pid_pcompose ⬝* _,
      replace loop_spaces_fun 2 with boundary_map,
      refine _ ⬝* pwhisker_left _ fiber_sequence_pequiv_loop_spaces_3_phomotopy⁻¹*,
      apply phomotopy_of_pinv_right_phomotopy,
      exact !pid_pcompose⁻¹*
    end
  | (k+3) :=
    begin
      replace (k + 3 + 1) with (k + 1 + 3),
      rewrite [fiber_sequence_pequiv_loop_spaces_add3 k,
               fiber_sequence_pequiv_loop_spaces_add3 (k+1)],
      refine !passoc ⬝* _,
      refine pwhisker_left _ (fiber_sequence_fun_phomotopy k) ⬝* _,
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
      apply pwhisker_right,
      replace (k + 1 + 3) with (k + 4),
      xrewrite [loop_spaces_fun_add3, pid_or_pinverse_add4, to_pmap_pequiv_trans],
      refine _ ⬝* !passoc⁻¹*,
      refine _ ⬝* pwhisker_left _ !passoc⁻¹*,
      refine _ ⬝* pwhisker_left _ (pwhisker_left _ !ap1_pcompose_pinverse),
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc ⬝* !passoc,
      apply pwhisker_right,
      refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose ⬝* pwhisker_right _ !ap1_pcompose,
      apply ap1_phomotopy,
      exact fiber_sequence_phomotopy_loop_spaces k
    end

  definition pid_or_pinverse_right : Π(n : ℕ), loop_spaces n →* loop_spaces n
  | 0     := !pid
  | 1     := !pid
  | 2     := !pid
  | (k+3) := Ω→(pid_or_pinverse_right k) ∘* pinverse

  definition pid_or_pinverse_left : Π(n : ℕ), loop_spaces n →* loop_spaces n
  | 0     := pequiv.rfl
  | 1     := pequiv.rfl
  | 2     := pequiv.rfl
  | 3     := pequiv.rfl
  | 4     := pequiv.rfl
  | (k+5) := Ω→(pid_or_pinverse_left (k+2)) ∘* pinverse

  definition pid_or_pinverse_right_add3 (n : ℕ)
    : pid_or_pinverse_right (n + 3) = Ω→(pid_or_pinverse_right n) ∘* pinverse :=
  by reflexivity

  definition pid_or_pinverse_left_add5 (n : ℕ)
    : pid_or_pinverse_left (n + 5) = Ω→(pid_or_pinverse_left (n+2)) ∘* pinverse :=
  by reflexivity

  theorem pid_or_pinverse_commute_right : Π(n : ℕ),
    loop_spaces_fun n ~* pid_or_pinverse_right n ∘* loop_spaces_fun n ∘* pid_or_pinverse (n + 1)
  | 0     := proof !pcompose_pid⁻¹* ⬝* !pid_pcompose⁻¹* qed
  | 1     := proof !pcompose_pid⁻¹* ⬝* !pid_pcompose⁻¹* qed
  | 2     := proof !pcompose_pid⁻¹* ⬝* !pid_pcompose⁻¹* qed
  | (k+3) :=
    begin
      replace (k + 3 + 1) with (k + 4),
      rewrite [pid_or_pinverse_right_add3, loop_spaces_fun_add3],
      refine _ ⬝* pwhisker_left _ (pwhisker_left _ !pid_or_pinverse_add4_rev⁻¹*),
      refine ap1_phomotopy (pid_or_pinverse_commute_right k) ⬝* _,
      refine !ap1_pcompose ⬝* _ ⬝* !passoc⁻¹*,
      apply pwhisker_left,
      refine !ap1_pcompose ⬝* _ ⬝* !passoc ⬝* !passoc,
      apply pwhisker_right,
      refine _ ⬝* pwhisker_right _ !ap1_pcompose_pinverse,
      refine _ ⬝* !passoc⁻¹*,
      refine !pcompose_pid⁻¹* ⬝* pwhisker_left _ _,
      symmetry, apply pinverse_pinverse
    end

  theorem pid_or_pinverse_commute_left : Π(n : ℕ),
    loop_spaces_fun n ∘* pid_or_pinverse_left (n + 1) ~* pid_or_pinverse n ∘* loop_spaces_fun n
  | 0     := proof !pcompose_pid ⬝* !pid_pcompose⁻¹* qed
  | 1     := proof !pcompose_pid ⬝* !pid_pcompose⁻¹* qed
  | 2     := proof !pcompose_pid ⬝* !pid_pcompose⁻¹* qed
  | 3     := proof !pcompose_pid ⬝* !pid_pcompose⁻¹* qed
  | (k+4) :=
    begin
      replace (k + 4 + 1) with (k + 5),
      rewrite [pid_or_pinverse_left_add5, pid_or_pinverse_add4, to_pmap_pequiv_trans],
      replace (k + 4) with (k + 1 + 3),
      rewrite [loop_spaces_fun_add3],
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc⁻¹*,
      refine _ ⬝* pwhisker_left _ !ap1_pcompose_pinverse,
      refine _ ⬝* !passoc,
      apply pwhisker_right,
      refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose,
      exact ap1_phomotopy (pid_or_pinverse_commute_left (k+1))
    end

  definition LES_of_loop_spaces' [constructor] : type_chain_complex +ℕ :=
  transfer_type_chain_complex
    fiber_sequence
    (λn, loop_spaces_fun n ∘* pid_or_pinverse (n + 1))
    fiber_sequence_pequiv_loop_spaces
    fiber_sequence_phomotopy_loop_spaces

  definition LES_of_loop_spaces [constructor] : type_chain_complex +ℕ :=
  type_chain_complex_cancel_aut
    LES_of_loop_spaces'
    loop_spaces_fun
    pid_or_pinverse
    pid_or_pinverse_right
    (λn x, idp)
    pid_or_pinverse_commute_right

  definition is_exact_LES_of_loop_spaces : is_exact_t LES_of_loop_spaces :=
  begin
    intro n,
    refine is_exact_at_t_cancel_aut n pid_or_pinverse_left _ _ pid_or_pinverse_commute_left _,
    apply is_exact_at_t_transfer,
    apply is_exact_fiber_sequence
  end

  open prod succ_str fin

  /--------------
      PART 3
   --------------/

  definition loop_spaces2 [reducible] : +3ℕ → Type*
  | (n, fin.mk 0 H) := Ω[n] Y
  | (n, fin.mk 1 H) := Ω[n] X
  | (n, fin.mk k H) := Ω[n] (pfiber f)

  definition loop_spaces2_add1 (n : ℕ) : Π(x : fin 3),
    loop_spaces2 (n+1, x) = Ω (loop_spaces2 (n, x))
  | (fin.mk 0 H) := by reflexivity
  | (fin.mk 1 H) := by reflexivity
  | (fin.mk 2 H) := by reflexivity
  | (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces_fun2 : Π(n : +3ℕ), loop_spaces2 (S n) →* loop_spaces2 n
  | (n, fin.mk 0 H) := proof Ω→[n] f qed
  | (n, fin.mk 1 H) := proof Ω→[n] (ppoint f) qed
  | (n, fin.mk 2 H) := proof Ω→[n] boundary_map ∘* loopn_succ_in Y n qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces_fun2_add1_0 (n : ℕ) (H : 0 < succ 2)
    : loop_spaces_fun2 (n+1, fin.mk 0 H) ~*
      cast proof idp qed ap1 (loop_spaces_fun2 (n, fin.mk 0 H)) :=
  by reflexivity

  definition loop_spaces_fun2_add1_1 (n : ℕ) (H : 1 < succ 2)
    : loop_spaces_fun2 (n+1, fin.mk 1 H) ~*
      cast proof idp qed ap1 (loop_spaces_fun2 (n, fin.mk 1 H)) :=
  by reflexivity

  definition loop_spaces_fun2_add1_2 (n : ℕ) (H : 2 < succ 2)
    : loop_spaces_fun2 (n+1, fin.mk 2 H) ~*
      cast proof idp qed ap1 (loop_spaces_fun2 (n, fin.mk 2 H)) :=
  proof !ap1_pcompose⁻¹* qed

  definition nat_of_str [unfold 2] [reducible] {n : ℕ} : ℕ × fin (succ n) → ℕ :=
  λx, succ n * pr1 x + val (pr2 x)

  definition str_of_nat {n : ℕ} : ℕ → ℕ × fin (succ n) :=
  λm, (m / (succ n), mk_mod n m)

  definition nat_of_str_3S [unfold 2] [reducible]
    : Π(x : stratified +ℕ 2), nat_of_str x + 1 = nat_of_str (@S (stratified +ℕ 2) x)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition fin_prod_nat_equiv_nat [constructor] (n : ℕ) : ℕ × fin (succ n) ≃ ℕ :=
  equiv.MK nat_of_str str_of_nat
    abstract begin
      intro m, unfold [nat_of_str, str_of_nat, mk_mod],
      refine _ ⬝ (eq_div_mul_add_mod m (succ n))⁻¹,
      rewrite [mul.comm]
    end end
    abstract begin
      intro x, cases x with m k,
      cases k with k H,
      apply prod_eq: esimp [str_of_nat],
      { rewrite [add.comm, add_mul_div_self_left _ _ (!zero_lt_succ), ▸*,
                 div_eq_zero_of_lt H, zero_add]},
      { apply eq_of_veq, esimp [mk_mod],
        rewrite [add.comm, add_mul_mod_self_left, ▸*, mod_eq_of_lt H]}
    end end

  /-
    note: in the following theorem the (n+1) case is 3 times the same,
    so maybe this can be simplified
  -/
  definition loop_spaces2_pequiv' : Π(n : ℕ) (x : fin (nat.succ 2)),
    loop_spaces (nat_of_str (n, x)) ≃* loop_spaces2 (n, x)
  |  0    (fin.mk 0 H)     := by reflexivity
  |  0    (fin.mk 1 H)     := by reflexivity
  |  0    (fin.mk 2 H)     := by reflexivity
  | (n+1) (fin.mk 0 H)     :=
    begin
      apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 0 H)
    end
  | (n+1) (fin.mk 1 H)     :=
    begin
      apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 1 H)
    end
  | (n+1) (fin.mk 2 H)     :=
    begin
      apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 2 H)
    end
  | n     (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces2_pequiv : Π(x : +3ℕ),
    loop_spaces (nat_of_str x) ≃* loop_spaces2 x
  | (n, x) := loop_spaces2_pequiv' n x

  local attribute loop_pequiv_loop [reducible]

  /- all cases where n>0 are basically the same -/
  definition loop_spaces_fun2_phomotopy (x : +3ℕ) :
    loop_spaces2_pequiv x ∘* loop_spaces_fun (nat_of_str x) ~*
      (loop_spaces_fun2 x ∘* loop_spaces2_pequiv (S x))
    ∘* pcast (ap (loop_spaces) (nat_of_str_3S x)) :=
  begin
    cases x with n x, cases x with k H,
    do 3 (cases k with k; rotate 1),
    { /-k≥3-/ exfalso, apply lt_le_antisymm H, apply le_add_left},
    { /-k=0-/
      induction n with n IH,
      { refine !pid_pcompose ⬝* _ ⬝* !pcompose_pid⁻¹* ⬝* !pcompose_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !pcompose_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ !loop_spaces_fun2_add1_0⁻¹*,
        refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose, apply ap1_phomotopy,
        exact IH ⬝* !pcompose_pid}},
    { /-k=1-/
      induction n with n IH,
      { refine !pid_pcompose ⬝* _ ⬝* !pcompose_pid⁻¹* ⬝* !pcompose_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !pcompose_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ !loop_spaces_fun2_add1_1⁻¹*,
        refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose, apply ap1_phomotopy,
        exact IH ⬝* !pcompose_pid}},
    { /-k=2-/
      induction n with n IH,
      { refine !pid_pcompose ⬝* _ ⬝* !pcompose_pid⁻¹*,
        refine !pcompose_pid⁻¹* ⬝* pconcat2 _ _,
        { exact (pcompose_pid (chain_complex.boundary_map f))⁻¹*},
        { refine !loop_pequiv_loop_rfl⁻¹* }},
      { refine _ ⬝* !pcompose_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ !loop_spaces_fun2_add1_2⁻¹*,
        refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose, apply ap1_phomotopy,
        exact IH ⬝* !pcompose_pid}},
  end

  definition LES_of_loop_spaces2 [constructor] : type_chain_complex +3ℕ :=
  transfer_type_chain_complex2
    LES_of_loop_spaces
    !fin_prod_nat_equiv_nat
    nat_of_str_3S
    @loop_spaces_fun2
    @loop_spaces2_pequiv
    begin
      intro m x,
      refine loop_spaces_fun2_phomotopy m x ⬝ _,
      apply ap (loop_spaces_fun2 m), apply ap (loop_spaces2_pequiv (S m)),
      esimp, exact ap010 cast !ap_compose⁻¹ x
    end

  definition is_exact_LES_of_loop_spaces2 : is_exact_t LES_of_loop_spaces2 :=
  begin
    intro n,
    apply is_exact_at_t_transfer2,
    apply is_exact_LES_of_loop_spaces
  end

  definition LES_of_homotopy_groups' [constructor] : chain_complex +3ℕ :=
  trunc_chain_complex LES_of_loop_spaces2

/--------------
    PART 4
 --------------/

  definition homotopy_groups [reducible] : +3ℕ → Set*
  | (n, fin.mk 0 H) := π[n] Y
  | (n, fin.mk 1 H) := π[n] X
  | (n, fin.mk k H) := π[n] (pfiber f)

  definition homotopy_groups_pequiv_loop_spaces2 [reducible]
    : Π(n : +3ℕ), ptrunc 0 (loop_spaces2 n) ≃* homotopy_groups n
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun : Π(n : +3ℕ), homotopy_groups (S n) →* homotopy_groups n
  | (n, fin.mk 0 H) := proof π→[n] f qed
  | (n, fin.mk 1 H) := proof π→[n] (ppoint f) qed
  | (n, fin.mk 2 H) :=
    proof π→[n] boundary_map ∘* homotopy_group_succ_in Y n qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun_phomotopy_loop_spaces_fun2 [reducible]
    : Π(n : +3ℕ), homotopy_groups_pequiv_loop_spaces2 n ∘* ptrunc_functor 0 (loop_spaces_fun2 n) ~*
      homotopy_groups_fun n ∘* homotopy_groups_pequiv_loop_spaces2 (S n)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) :=
    begin
      refine !pid_pcompose ⬝* _ ⬝* !pcompose_pid⁻¹*,
      refine !ptrunc_functor_pcompose
    end
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition LES_of_homotopy_groups [constructor] : chain_complex +3ℕ :=
  transfer_chain_complex
    LES_of_homotopy_groups'
    homotopy_groups_fun
    homotopy_groups_pequiv_loop_spaces2
    homotopy_groups_fun_phomotopy_loop_spaces_fun2

  definition is_exact_LES_of_homotopy_groups : is_exact LES_of_homotopy_groups :=
  begin
    intro n,
    apply is_exact_at_transfer,
    apply is_exact_at_trunc,
    apply is_exact_LES_of_loop_spaces2
  end

  variable (n : ℕ)

  /- the carrier of the fiber sequence is definitionally what we want (as pointed sets) -/
  example : LES_of_homotopy_groups (str_of_nat 6)  = π[2] Y          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 7)  = π[2] X          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 8)  = π[2] (pfiber f) :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 9)  = π[3] Y          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 10) = π[3] X          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 11) = π[3] (pfiber f) :> Set* := by reflexivity

  definition LES_of_homotopy_groups_0 : LES_of_homotopy_groups (n, 0) = π[n] Y :=
  by reflexivity
  definition LES_of_homotopy_groups_1 : LES_of_homotopy_groups (n, 1) = π[n] X :=
  by reflexivity
  definition LES_of_homotopy_groups_2 : LES_of_homotopy_groups (n, 2) = π[n] (pfiber f) :=
  by reflexivity

  /-
    the functions of the fiber sequence is definitionally what we want (as pointed function).
  -/

  definition LES_of_homotopy_groups_fun_0 :
    cc_to_fn LES_of_homotopy_groups (n, 0) = π→[n] f :=
  by reflexivity
  definition LES_of_homotopy_groups_fun_1 :
    cc_to_fn LES_of_homotopy_groups (n, 1) = π→[n] (ppoint f) :=
  by reflexivity
  definition LES_of_homotopy_groups_fun_2 : cc_to_fn LES_of_homotopy_groups (n, 2) =
    π→[n] boundary_map ∘* homotopy_group_succ_in Y n :=
  by reflexivity

  open group

  definition group_LES_of_homotopy_groups (n : ℕ) : Π(x : fin (succ 2)),
    group (LES_of_homotopy_groups (n + 1, x))
  | (fin.mk 0     H) := begin rexact group_homotopy_group n Y end
  | (fin.mk 1     H) := begin rexact group_homotopy_group n X end
  | (fin.mk 2     H) := begin rexact group_homotopy_group n (pfiber f) end
  | (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition ab_group_LES_of_homotopy_groups (n : ℕ) : Π(x : fin (succ 2)),
    ab_group (LES_of_homotopy_groups (n + 2, x))
  | (fin.mk 0 H) := proof ab_group_homotopy_group n Y qed
  | (fin.mk 1 H) := proof ab_group_homotopy_group n X qed
  | (fin.mk 2 H) := proof ab_group_homotopy_group n (pfiber f) qed
  | (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition Group_LES_of_homotopy_groups (x : +3ℕ) : Group.{u} :=
  Group.mk (LES_of_homotopy_groups (nat.succ (pr1 x), pr2 x))
              (group_LES_of_homotopy_groups (pr1 x) (pr2 x))

  definition AbGroup_LES_of_homotopy_groups (n : +3ℕ) : AbGroup.{u} :=
  AbGroup.mk (LES_of_homotopy_groups (pr1 n + 2, pr2 n))
                  (ab_group_LES_of_homotopy_groups (pr1 n) (pr2 n))

  definition homomorphism_LES_of_homotopy_groups_fun : Π(k : +3ℕ),
    Group_LES_of_homotopy_groups (S k) →g Group_LES_of_homotopy_groups k
  | (k, fin.mk 0 H) :=
    proof homomorphism.mk (cc_to_fn LES_of_homotopy_groups (k + 1, 0))
                          (homotopy_group_functor_mul _ _) qed
  | (k, fin.mk 1 H) :=
    proof homomorphism.mk (cc_to_fn LES_of_homotopy_groups (k + 1, 1))
                          (homotopy_group_functor_mul _ _) qed
  | (k, fin.mk 2 H) :=
    begin
      apply homomorphism.mk (cc_to_fn LES_of_homotopy_groups (k + 1, 2)),
      exact abstract begin rewrite [LES_of_homotopy_groups_fun_2],
      refine homomorphism.struct ((π→g[k+1] boundary_map) ∘g ghomotopy_group_succ_in Y k),
      end end
    end
  | (k, fin.mk (l+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  end

  /-
    Fibration sequences

    This is a similar construction, but with as input data two pointed maps,
    and a pointed equivalence between the domain of the second map and the fiber of the first map,
    and a pointed homotopy.
  -/

  section
  universe variable u
  parameters {F X Y : pType.{u}} (f : X →* Y) (g : F →* X) (e : pfiber f ≃* F)
             (p : ppoint f ~* g ∘* e)
  include f p
  open succ_str prod nat
  definition fibration_sequence_car [reducible] : +3ℕ → Type*
  | (n, fin.mk 0 H) := Ω[n] Y
  | (n, fin.mk 1 H) := Ω[n] X
  | (n, fin.mk k H) := Ω[n] F

  definition fibration_sequence_fun
    : Π(n : +3ℕ), fibration_sequence_car (S n) →* fibration_sequence_car n
  | (n, fin.mk 0 H) := proof Ω→[n] f qed
  | (n, fin.mk 1 H) := proof Ω→[n] g qed
  | (n, fin.mk 2 H) := proof Ω→[n] (e ∘* boundary_map f) ∘* loopn_succ_in Y n qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition fibration_sequence_pequiv : Π(x : +3ℕ),
     loop_spaces2 f x ≃* fibration_sequence_car x
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := loopn_pequiv_loopn n e
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition fibration_sequence_fun_phomotopy : Π(x : +3ℕ),
    fibration_sequence_pequiv x ∘* loop_spaces_fun2 f x ~*
      (fibration_sequence_fun x ∘* fibration_sequence_pequiv (S x))
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) :=
    begin refine !pid_pcompose ⬝* _, refine apn_phomotopy n p ⬝* _,
      refine !apn_pcompose ⬝* _, reflexivity end
  | (n, fin.mk 2 H) := begin refine !passoc⁻¹* ⬝* _ ⬝* !pcompose_pid⁻¹*, apply pwhisker_right,
      refine _ ⬝* !apn_pcompose⁻¹*, reflexivity end
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition type_fibration_sequence [constructor] : type_chain_complex +3ℕ :=
  transfer_type_chain_complex
    (LES_of_loop_spaces2 f)
    fibration_sequence_fun
    fibration_sequence_pequiv
    fibration_sequence_fun_phomotopy

  definition is_exact_type_fibration_sequence : is_exact_t type_fibration_sequence :=
  begin
    intro n,
    apply is_exact_at_t_transfer,
    apply is_exact_LES_of_loop_spaces2
  end

  definition fibration_sequence [constructor] : chain_complex +3ℕ :=
  trunc_chain_complex type_fibration_sequence

  end


end chain_complex
