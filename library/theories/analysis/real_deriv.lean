/-
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Derivatives on ℝ
-/
import .bounded_linear_operator
open real nat classical topology analysis
noncomputable theory

namespace real

-- move this to group
theorem add_sub_self (a b : ℝ) : a + b - a = b :=
  by rewrite [add_sub_assoc, add.comm, sub_add_cancel]

-- make instance of const mul bdd lin op?

definition derivative_at (f : ℝ → ℝ) (d x : ℝ) := is_frechet_deriv_at f (λ t, d • t) x

theorem derivative_at_intro (f : ℝ → ℝ) (d x : ℝ) (H : (λ h, (f (x + h) - f x) / h) ⟶ d at 0) :
        derivative_at f d x :=
  begin
    apply is_frechet_deriv_at_intro,
    intros ε Hε,
    cases H Hε with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro y Hy,
    rewrite [-sub_zero y at Hy{2}],
    note Hδ' := and.right Hδ y Hy,
    have Hδ'' : abs ((f (x + y) - f x - d * y) / y) < ε,
      by rewrite [-div_sub_div_same, mul_div_cancel _ (and.left Hy)]; apply Hδ',
    show abs (f (x + y) - f x - d * y) / abs y < ε, by rewrite -abs_div; apply Hδ''
  end

theorem deriv_at_const (c x : ℝ) : derivative_at (λ t, c) 0 x :=
  begin
    apply derivative_at_intro,
    have (λ h, (c - c) / h) = (λ h, 0), from funext (λ h, by rewrite [sub_self, zero_div]),
    rewrite this,
    apply converges_to_at_constant
  end

theorem deriv_at_id (x : ℝ) : derivative_at (λ t, t) 1 x :=
  begin
    apply derivative_at_intro,
    apply converges_to_at_real_intro,
    intros ε Hε,
    existsi 1,
    split,
    exact zero_lt_one,
    intros x' Hx',
    rewrite [add_sub_self, div_self (and.left Hx'), sub_self, abs_zero],
    exact Hε
  end

end real
