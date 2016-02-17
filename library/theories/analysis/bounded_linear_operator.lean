/-
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Bounded linear operators
-/
import .normed_space .real_limit algebra.module
open real nat classical
noncomputable theory

namespace analysis

section bdd_lin_op

structure is_bdd_linear_map [class] {V W : Type} [normed_vector_space V] [normed_vector_space W] (f : V → W) extends is_linear_map ℝ f :=
  (op_norm : ℝ) (op_norm_pos : op_norm > 0) (op_norm_bound : ∀ v : V, ∥f v∥ ≤ op_norm * ∥v∥)

/-theorem is_bdd_linear_map_id [instance] (V : Type) [normed_vector_space V] : is_bdd_linear_map (λ a : V, a) :=
   sorry-/

theorem is_bdd_linear_map_add [instance] {V W : Type} [normed_vector_space V] [normed_vector_space W]
        (f g : V → W) [Hbf : is_bdd_linear_map f] [Hbg : is_bdd_linear_map g] :
        is_bdd_linear_map (λ x, f x + g x) :=
  begin
    fapply is_bdd_linear_map.mk,
    {intros,
    rewrite [linear_map_additive ℝ f, linear_map_additive ℝ g],
    simp},
    {intros,
    rewrite [linear_map_homogeneous f, linear_map_homogeneous g, smul_left_distrib]},
    {exact is_bdd_linear_map.op_norm _ _ f + is_bdd_linear_map.op_norm _ _ g},
    {apply add_pos,
    repeat apply is_bdd_linear_map.op_norm_pos},
    {intro,
    apply le.trans,
    apply norm_triangle,
    rewrite right_distrib,
    apply add_le_add,
    repeat apply is_bdd_linear_map.op_norm_bound}
  end

variables {V W : Type}
variables [HV : normed_vector_space V] [HW : normed_vector_space W]
--variable f : V → W --linear_operator V W
include HV HW
variable f : V → W
variable [Hf : is_bdd_linear_map f]
include Hf

definition op_norm := is_bdd_linear_map.op_norm _ _ f

theorem op_norm_pos : op_norm f > 0 := is_bdd_linear_map.op_norm_pos _ _ f

theorem op_norm_bound (v : V) : ∥f v∥ ≤ (op_norm f) * ∥v∥ := is_bdd_linear_map.op_norm_bound  _ _ f v

theorem bounded_linear_operator_continuous : continuous f :=
  begin
    intro x,
    apply normed_vector_space.continuous_at_intro,
    intro ε Hε,
    existsi ε / (op_norm f),
    split,
    apply div_pos_of_pos_of_pos Hε !op_norm_pos,
    intro x' Hx',
    rewrite [-linear_map_sub f],
    apply lt_of_le_of_lt,
    apply op_norm_bound f,
    rewrite [-@mul_div_cancel' _ _ ε (op_norm f) (ne_of_gt !op_norm_pos)],
    apply mul_lt_mul_of_pos_left,
    exact Hx',
    apply op_norm_pos
  end

end bdd_lin_op

section frechet_deriv
variables {V W : Type}
variables [HV : normed_vector_space V] [HW : normed_vector_space W]
include HV HW

open topology

definition is_frechet_deriv_at (f A : V → W) [is_bdd_linear_map A] (x : V) :=
  (λ h : V, ∥f (x + h) - f x - A h ∥ / ∥ h ∥) ⟶ 0 at 0

structure frechet_diffable_at [class] (f : V → W) (x : V) :=
  (A : V → W) [HA : is_bdd_linear_map A] (is_fr_der : is_frechet_deriv_at f A x)

variables f g : V → W
variable x : V

definition frechet_deriv_at [Hf : frechet_diffable_at f x] : V → W :=
  frechet_diffable_at.A _ _ f x

definition frechet_deriv_at_is_bdd_linear_map [instance] (f : V → W) (x : V) [Hf : frechet_diffable_at f x] :
           is_bdd_linear_map (frechet_deriv_at f x) :=
  frechet_diffable_at.HA _ _ f x

theorem frechet_deriv_spec [Hf : frechet_diffable_at f x] :
        (λ h : V, ∥f (x + h) - f x - (frechet_deriv_at f x h) ∥ / ∥ h ∥) ⟶ 0 at 0 :=
  frechet_diffable_at.is_fr_der _ _ f x

theorem frechet_diffable_at_add (A B : V → W) [is_bdd_linear_map A] [is_bdd_linear_map B]
        (Hf : is_frechet_deriv_at f A x) (Hg : is_frechet_deriv_at g B x) :
        is_frechet_deriv_at (λ y, f y + g y) (λ y, A y + B y) x :=
  begin
    rewrite ↑is_frechet_deriv_at,
    have Hle : ∀ h, ∥f (x + h) + g (x + h) - (f x + g x) - (A h + B h)∥ / ∥h∥ ≤
                  ∥f (x + h) - f x - A h∥ / ∥h∥ + ∥g (x + h) - g x - B h∥ / ∥h∥, begin
      intro h,
      cases em (∥h∥ > 0) with Hh Hh,
      krewrite div_add_div_same,
      apply div_le_div_of_le_of_pos,
      have Hfeq : f (x + h) + g (x + h) - (f x + g x) - (A h + B h) =
                       (f (x + h) - f x - A h) + (g (x + h) - g x - B h), by simp,
      rewrite Hfeq,
      apply norm_triangle,
      exact Hh,
      have Hhe : ∥h∥ = 0, from eq_of_le_of_ge (le_of_not_gt Hh) !norm_nonneg,
      krewrite [Hhe, *div_zero, zero_add],
      eapply le.refl
    end,
    have Hlimge : (λ h, ∥f (x + h) - f x - A h∥ / ∥h∥ + ∥g (x + h) - g x - B h∥ / ∥h∥) ⟶ 0 at 0, begin
      rewrite [-zero_add 0],
      apply add_converges_to_at,
      apply Hf,
      apply Hg
    end,
    have Hlimle : (λ (h : V), (0 : ℝ)) ⟶ 0 at 0, from converges_to_at_constant 0 0,
    apply converges_to_at_squeeze Hlimle Hlimge,
    intro y,
    apply div_nonneg_of_nonneg_of_nonneg,
    repeat apply norm_nonneg,
    apply Hle
  end

/-theorem continuous_at_of_diffable_at [Hf : frechet_diffable_at f x] : continuous_at f x :=
  begin
    apply normed_vector_space.continuous_at_intro,
    intros ε Hε,
    note Hfds := frechet_deriv_spec f x Hε,
    cases Hfds with δ Hδ,
    cases Hδ with Hδ Hδ',
    existsi δ,
    split,
    assumption,
    intro x' Hx',
    have Hx'x : x' - x ≠ 0 ∧ dist (x' - x) 0 < δ, from sorry,
    note Hδ'' := Hδ' Hx'x,

  end-/

end frechet_deriv

end analysis
