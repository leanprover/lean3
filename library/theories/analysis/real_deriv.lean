/-
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Derivatives on ℝ
-/
import .bounded_linear_operator
open real nat classical topology analysis set
noncomputable theory

namespace real

-- move this to group
theorem add_sub_self (a b : ℝ) : a + b - a = b :=
  by rewrite [add_sub_assoc, add.comm, sub_add_cancel]

-- make instance of const mul bdd lin op?

definition derivative_at (f : ℝ → ℝ) (d x : ℝ) := is_frechet_deriv_at f (λ t, d • t) x

theorem derivative_at_intro (f : ℝ → ℝ) (d x : ℝ) (H : (λ h, (f (x + h) - f x) / h) ⟶ d [at 0]) :
        derivative_at f d x :=
  begin
    apply is_frechet_deriv_at_intro,
    intros ε Hε,
    cases approaches_at_dest H Hε with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro y Hy,
    rewrite [-sub_zero y at Hy{2}],
    note Hδ' := and.right Hδ y (and.right Hy) (and.left Hy),
    have Hδ'' : abs ((f (x + y) - f x - d * y) / y) < ε,
      by rewrite [-div_sub_div_same, mul_div_cancel _ (and.left Hy)]; apply Hδ',
    show abs (f (x + y) - f x - d * y) / abs y < ε, by rewrite -abs_div; apply Hδ''
  end

theorem derivative_at_of_frechet_derivative_at {f g : ℝ → ℝ} [is_bdd_linear_map g] {d x : ℝ}
        (H : is_frechet_deriv_at f g x) (Hg : g = λ x, d * x) :
        derivative_at f d x :=
  by apply is_frechet_deriv_at_of_eq H Hg

theorem deriv_at_const (c x : ℝ) : derivative_at (λ t, c) 0 x :=
  derivative_at_of_frechet_derivative_at
    (@frechet_deriv_at_const ℝ ℝ _ _ _ c)
    (funext (λ v, by rewrite zero_mul))

theorem deriv_at_id (x : ℝ) : derivative_at (λ t, t) 1 x :=
  derivative_at_of_frechet_derivative_at
    (@frechet_deriv_at_id ℝ ℝ _ _ _)
    (funext (λ v, by rewrite one_mul))

theorem deriv_at_mul {f : ℝ → ℝ} {d x : ℝ} (H : derivative_at f d x) (c : ℝ) :
        derivative_at (λ t, c * f t) (c * d) x :=
  derivative_at_of_frechet_derivative_at
    (frechet_deriv_at_smul _ _ c H)
    (funext (λ v, by rewrite mul.assoc))

end real
