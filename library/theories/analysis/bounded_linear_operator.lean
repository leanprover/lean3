/-
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Bounded linear operators
-/
import .normed_space .real_limit algebra.module algebra.homomorphism
open real nat classical topology
noncomputable theory

namespace analysis

-- define bounded linear operators and basic instances
section bdd_lin_op
structure is_bdd_linear_map [class] {V W : Type} [normed_vector_space V] [normed_vector_space W] (f : V → W)
          extends is_module_hom ℝ f :=
  (op_norm : ℝ) (op_norm_pos : op_norm > 0) (op_norm_bound : ∀ v : V, ∥f v∥ ≤ op_norm * ∥v∥)

theorem is_bdd_linear_map_id [instance] (V : Type) [normed_vector_space V] : is_bdd_linear_map (λ x : V, x) :=
  begin
    fapply is_bdd_linear_map.mk,
    repeat (intros; reflexivity),
    exact 1,
    exact zero_lt_one,
    intro, rewrite one_mul, apply le.refl
  end

theorem is_bdd_linear_map_zero [instance] (V W : Type) [normed_vector_space V] [normed_vector_space W] :
        is_bdd_linear_map (λ x : V, (0 : W)) :=
  begin
    fapply is_bdd_linear_map.mk,
    all_goals intros,
    rewrite zero_add,
    rewrite smul_zero,
    exact 1,
    exact zero_lt_one,
    rewrite [norm_zero, one_mul],
    apply norm_nonneg
  end

theorem is_bdd_linear_map_add [instance] {V W : Type} [normed_vector_space V] [normed_vector_space W]
        (f g : V → W) [Hbf : is_bdd_linear_map f] [Hbg : is_bdd_linear_map g] :
        is_bdd_linear_map (λ x, f x + g x) :=
  begin
    fapply is_bdd_linear_map.mk,
    all_goals intros,
    {rewrite [hom_add f, hom_add g],-- (this takes 4 seconds: rewrite [2 hom_add])
    simp},
    {rewrite [hom_smul f, hom_smul g, smul_left_distrib]},
    {exact is_bdd_linear_map.op_norm _ _ f + is_bdd_linear_map.op_norm _ _ g},
    {apply add_pos,
    repeat apply is_bdd_linear_map.op_norm_pos},
    {apply le.trans,
    apply norm_triangle,
    rewrite right_distrib,
    apply add_le_add,
    repeat apply is_bdd_linear_map.op_norm_bound}
  end

theorem is_bdd_linear_map_smul [instance] {V W : Type} [normed_vector_space V] [normed_vector_space W]
        (f : V → W) (c : ℝ) [Hbf : is_bdd_linear_map f] : is_bdd_linear_map (λ x, c • f x) :=
  begin
    apply @decidable.cases_on (c = 0),
    exact _,
    {intro Hcz,
    rewrite Hcz,
    have Hfe : (λ x : V, (0 : ℝ) • f x) = (λ x : V, 0), from funext (λ x, !zero_smul),
    rewrite Hfe,
    apply is_bdd_linear_map_zero},
    intro Hcnz,
    fapply is_bdd_linear_map.mk,
    all_goals intros,
    {rewrite [hom_add f, smul_left_distrib]},
    {rewrite [hom_smul f, -*mul_smul, {c*r}mul.comm]},
    {exact (abs c) * is_bdd_linear_map.op_norm _ _ f},
    {have Hpos : abs c > 0, from abs_pos_of_ne_zero Hcnz,
    apply mul_pos,
    assumption,
    apply is_bdd_linear_map.op_norm_pos},
    {rewrite [norm_smul, mul.assoc],
    apply mul_le_mul_of_nonneg_left,
    apply is_bdd_linear_map.op_norm_bound,
    apply abs_nonneg}
  end

theorem is_bdd_linear_map_neg [instance] {V W : Type} [normed_vector_space V] [normed_vector_space W]
        (f : V → W) [Hbf : is_bdd_linear_map f] : is_bdd_linear_map (λ x, -f x) :=
  begin
    have H : (λ x : V, -f x) = (λ x : V, (-1 : ℝ) • f x), from funext (λ x, eq.symm !neg_one_smul),
    rewrite H,
    apply is_bdd_linear_map_smul
  end

-- this can't be an instance because things loop
theorem is_bdd_linear_map_comp {U V W : Type} [normed_vector_space U] [normed_vector_space V]
        [normed_vector_space W] (f : V → W) (g : U → V) [is_bdd_linear_map f] [is_bdd_linear_map g] :
        is_bdd_linear_map (λ u, f (g u)) :=
  begin
    fapply is_bdd_linear_map.mk,
    all_goals intros,
    {rewrite [hom_add g, hom_add f]},
    {rewrite [hom_smul g, hom_smul f]},
    {exact is_bdd_linear_map.op_norm _ _ f * is_bdd_linear_map.op_norm _ _ g},
    {apply mul_pos, repeat apply is_bdd_linear_map.op_norm_pos},
    {apply le.trans,
    apply is_bdd_linear_map.op_norm_bound _ _ f,
    apply le.trans,
    apply mul_le_mul_of_nonneg_left,
    apply is_bdd_linear_map.op_norm_bound _ _ g,
    apply le_of_lt !is_bdd_linear_map.op_norm_pos,
    rewrite *mul.assoc,
    apply le.refl}
  end

variables {V W : Type}
variables [HV : normed_vector_space V] [HW : normed_vector_space W]
include HV HW
variable f : V → W
variable [Hf : is_bdd_linear_map f]
include Hf

definition op_norm := is_bdd_linear_map.op_norm _ _ f

theorem op_norm_pos : op_norm f > 0 := is_bdd_linear_map.op_norm_pos _ _ f

theorem op_norm_bound (v : V) : ∥f v∥ ≤ (op_norm f) * ∥v∥ := is_bdd_linear_map.op_norm_bound  _ _ f v

theorem bounded_linear_operator_continuous : continuous f :=
  begin
    apply continuous_of_forall_continuous_at,
    intro x,
    apply normed_vector_space.continuous_at_intro,
    intro ε Hε,
    existsi ε / (op_norm f),
    split,
    apply div_pos_of_pos_of_pos Hε !op_norm_pos,
    intro x' Hx',
    rewrite [-hom_sub f],
    apply lt_of_le_of_lt,
    apply op_norm_bound f,
    rewrite [-@mul_div_cancel' _ _ ε (op_norm f) (ne_of_gt !op_norm_pos)],
    apply mul_lt_mul_of_pos_left,
    exact Hx',
    apply op_norm_pos
  end

end bdd_lin_op


-- define Frechet derivative and basic properties

section frechet_deriv
variables {V W : Type}
variables [HV : normed_vector_space V] [HW : normed_vector_space W]
include HV HW

definition is_frechet_deriv_at (f A : V → W) [is_bdd_linear_map A] (x : V) :=
  (λ h : V, ∥f (x + h) - f x - A h ∥ / ∥ h ∥) ⟶ 0 at 0

theorem is_frechet_deriv_at_intro {f A : V → W} [is_bdd_linear_map A] {x : V}
        (H : ∀ ⦃ε : ℝ⦄, ε > 0 →
              (∃ δ : ℝ, δ > 0 ∧ ∀ ⦃x' : V⦄, x' ≠ 0 ∧ ∥x'∥ < δ → ∥f (x + x') - f x - A x'∥ / ∥x'∥ < ε)) :
        is_frechet_deriv_at f A x :=
  begin
    intros ε Hε,
    cases H Hε with δ Hδ,
    cases Hδ with Hδ Hδ',
    existsi δ,
    split,
    assumption,
    intros x' Hx',
    cases Hx' with Hx'1 Hx'2,
    show abs (∥f (x + x') - f x - A x'∥ / ∥x'∥ - 0) < ε, begin
      have H : ∥f (x + x') - f x - A x'∥ / ∥x'∥ ≥ 0,
        from div_nonneg_of_nonneg_of_nonneg !norm_nonneg !norm_nonneg,
      rewrite [sub_zero, abs_of_nonneg H],
      apply Hδ',
      split,
      assumption,
      rewrite [-sub_zero x'],
      apply Hx'2
    end
  end

theorem is_frechet_deriv_at_elim {f A : V → W} [is_bdd_linear_map A] {x : V} (H : is_frechet_deriv_at f A x) :
         ∀ ⦃ε : ℝ⦄, ε > 0 →
              (∃ δ : ℝ, δ > 0 ∧ ∀ ⦃x' : V⦄, x' ≠ 0 ∧ ∥x'∥ < δ → ∥f (x + x') - f x - A x'∥ / ∥x'∥ < ε) :=
  begin
    intros ε Hε,
    cases H Hε with δ Hδ,
    cases Hδ with Hδ Hδ',
    existsi δ,
    split,
    assumption,
    intros x' Hx',
    rewrite [-sub_zero x' at Hx' {2}],
    have Hδ'' : abs (∥f (x + x') - f x - A x'∥ / ∥x'∥ - 0) < ε, from Hδ' Hx',
    have Hpos : ∥f (x + x') - f x - A x'∥ / ∥x'∥ ≥ 0, from div_nonneg_of_nonneg_of_nonneg !norm_nonneg !norm_nonneg,
    rewrite [sub_zero at Hδ'', abs_of_nonneg Hpos at Hδ''],
    assumption
  end

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

theorem frechet_deriv_at_const (w : W) : is_frechet_deriv_at (λ v : V, w) (λ v : V, 0) x :=
  begin
    intros ε Hε,
    existsi 1,
    split,
    exact zero_lt_one,
    intros x' Hx',
    rewrite [sub_self, sub_zero, norm_zero],
    krewrite [zero_div, dist_self],
    assumption
  end

theorem frechet_deriv_at_smul {c : ℝ} {A : V → W} [is_bdd_linear_map A]
        (Hf : is_frechet_deriv_at f A x) : is_frechet_deriv_at (λ y, c • f y) (λ y, c • A y) x :=
  begin
    eapply @decidable.cases_on (abs c = 0),
    exact _,
    {intro Hc,
    have Hz : c = 0, from eq_zero_of_abs_eq_zero Hc,
    have Hfz : (λ y : V, (0 : ℝ) • f y) = (λ y : V, 0), from funext (λ y, !zero_smul),
    --have Hfz' : (λ x : V, (0 : ℝ) • A x) = (λ x : V, 0), from funext (λ y, !zero_smul),
    -- rewriting Hfz' produces type-incorrect term
    rewrite [Hz, Hfz, ↑is_frechet_deriv_at],
    intro ε Hε,
    existsi 1,
    split,
    exact zero_lt_one,
    intro x' Hx',
    rewrite [zero_smul, *sub_zero, norm_zero],
    krewrite [zero_div, dist_self],
    exact Hε},
    intro Hcnz,
    rewrite ↑is_frechet_deriv_at,
    intros ε Hε,
    have Hεc : ε / abs c > 0, from div_pos_of_pos_of_pos Hε (lt_of_le_of_ne !abs_nonneg (ne.symm Hcnz)),
    cases Hf Hεc with δ Hδ,
    cases Hδ with Hδp Hδ,
    existsi δ,
    split,
    assumption,
    intro x' Hx',
    show abs ((∥c • f (x + x') - c • f x - c • A x'∥ / ∥x'∥ - 0)) < ε, begin
      rewrite [sub_zero, -2 smul_sub_left_distrib, norm_smul],
      krewrite mul_div_assoc,
      rewrite [abs_mul, abs_abs, -{ε}mul_div_cancel' Hcnz],
      apply mul_lt_mul_of_pos_left,
      have Hδ' : abs (∥f (x + x') - f x - A x'∥ / ∥x'∥ - 0) < ε / abs c, from Hδ Hx',
      rewrite sub_zero at Hδ',
      apply Hδ',
      apply lt_of_le_of_ne,
      apply abs_nonneg,
      apply ne.symm,
      apply Hcnz
    end
  end

theorem frechet_deriv_at_neg {A : V → W} [is_bdd_linear_map A]
        (Hf : is_frechet_deriv_at f A x) : is_frechet_deriv_at (λ y, - f y) (λ y, - A y) x :=
  begin
    apply is_frechet_deriv_at_intro,
    intros ε Hε,
    cases is_frechet_deriv_at_elim Hf Hε with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro x' Hx',
    rewrite [-norm_neg, neg_sub, sub_neg_eq_add, sub_add_eq_sub_sub, sub_neg_eq_add,
             add_sub_assoc, add.comm, -sub_eq_add_neg],
    apply and.right Hδ,
    assumption
  end

theorem frechet_deriv_at_add (A B : V → W) [is_bdd_linear_map A] [is_bdd_linear_map B]
        (Hf : is_frechet_deriv_at f A x) (Hg : is_frechet_deriv_at g B x) :
        is_frechet_deriv_at (λ y, f y + g y) (λ y, A y + B y) x :=
  begin
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

open topology

theorem continuous_at_of_diffable_at [Hf : frechet_diffable_at f x] : continuous_at f x :=
  begin
    apply normed_vector_space.continuous_at_intro,
    intros ε Hε,
    note Hfds := frechet_deriv_spec f x Hε,
    cases Hfds with δ Hδ,
    cases Hδ with Hδ Hδ',
    existsi min δ ((ε / 2) / (ε + op_norm (frechet_deriv_at f x))),
    split,
    {apply lt_min,
    exact Hδ,
    repeat apply div_pos_of_pos_of_pos,
    exact Hε,
    apply two_pos,
    apply add_pos Hε !op_norm_pos},
    {intro x' Hx',
    cases em (x' - x = 0) with Heq Hneq,
    rewrite [eq_of_sub_eq_zero Heq, sub_self, norm_zero], assumption,
    have Hx'x : x' - x ≠ 0 ∧ dist (x' - x) 0 < δ, from and.intro Hneq begin
      change ∥(x' - x) - 0∥ < δ,
      rewrite sub_zero,
      apply lt_of_lt_of_le,
      apply Hx',
      apply min_le_left
    end,
    have Hx'xp : ∥x' - x∥ > 0, from norm_pos_of_ne_zero Hneq,
    have Hδ'' : abs (∥f (x + (x' - x)) - f x - frechet_deriv_at f x (x' - x)∥ / ∥x' - x∥ - 0) < ε, from Hδ' Hx'x,
    have Hnn : ∥f (x + (x' - x)) - f x - frechet_deriv_at f x (x' - x)∥ / ∥x' - x∥ ≥ 0,
      from div_nonneg_of_nonneg_of_nonneg !norm_nonneg !norm_nonneg,
    rewrite [sub_zero at Hδ'', abs_of_nonneg Hnn at Hδ'', add.comm at Hδ'', sub_add_cancel at Hδ''],
    note H1 := lt_mul_of_div_lt_of_pos Hx'xp Hδ'',
    have H2 : f x' - f x = f x' - f x - frechet_deriv_at f x (x' - x) + frechet_deriv_at f x (x' - x),
      by rewrite sub_add_cancel,  --by simp, (simp takes .5 seconds to do this!)
    rewrite H2,
    apply lt_of_le_of_lt,
    apply norm_triangle,
    apply lt.trans,
    apply add_lt_add_of_lt_of_le,
    apply H1,
    apply op_norm_bound (!frechet_deriv_at),
    rewrite [-add_halves ε at {2}],
    apply add_lt_add,
    let on := op_norm (frechet_deriv_at f x),
    exact calc
      ε * ∥x' - x∥ < ε * min δ ((ε / 2) / (ε + on)) : mul_lt_mul_of_pos_left Hx' Hε
              ... ≤ ε * ((ε / 2) / (ε + on)) : mul_le_mul_of_nonneg_left !min_le_right (le_of_lt Hε)
              ... < ε / 2 : mul_div_self_add_lt (div_pos_of_pos_of_pos Hε two_pos) Hε !op_norm_pos,
    exact calc
      on * ∥x' - x∥ < on * min δ ((ε / 2) / (ε + on)) : mul_lt_mul_of_pos_left Hx' !op_norm_pos
               ... ≤ on * ((ε / 2) / (ε + on)) : mul_le_mul_of_nonneg_left !min_le_right (le_of_lt !op_norm_pos)
               ... < ε / 2 : mul_div_add_self_lt (div_pos_of_pos_of_pos Hε two_pos) Hε !op_norm_pos}
  end

end frechet_deriv

/-section comp

variables {U V W : Type}
variables [HU : normed_vector_space U] [HV : normed_vector_space V] [HW : normed_vector_space W]
variables {f : V → W} {g : U → V}
variables {A : V → W} {B : U → V}
variables [HA : is_bdd_linear_map A] [HB : is_bdd_linear_map B]
variable {x : U}
include HU HV HW HA HB

theorem frechet_derivative_at_comp (Hg : is_frechet_deriv_at g B x) (Hf : is_frechet_deriv_at f A (g x)) :
        @is_frechet_deriv_at _ _ _ _ (λ y, f (g y)) (λ y, A (B y)) !is_bdd_linear_map_comp x :=
  begin
    rewrite ↑is_frechet_deriv_at,
    intros ε Hε,
  end

end comp-/

end analysis
