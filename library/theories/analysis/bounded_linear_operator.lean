/-
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Bounded linear operators
-/
import .normed_space .real_limit algebra.module algebra.homomorphism
open real nat classical topology set
--open normed_vector_space (this confuses lots of stuff??)
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

theorem bdd_linear_map_continuous : continuous f :=
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

definition has_frechet_deriv_at (f A : V → W) [is_bdd_linear_map A] (x : V) :=
  (λ h : V, ∥f (x + h) - f x - A h ∥ / ∥ h ∥) ⟶ 0 [at 0]

lemma diff_quot_cts {f A : V → W} [HA : is_bdd_linear_map A] {y : V} (Hf : has_frechet_deriv_at f A y) :
      continuous_at (λ h, ∥f (y + h) - f y - A h∥ / ∥h∥) 0 :=
  begin
    apply normed_vector_space.continuous_at_intro,
    intro ε Hε,
    cases normed_vector_space.approaches_at_dest Hf Hε with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro x' Hx',
    cases em (x' = 0) with Heq Hneq,
    {rewrite [Heq, norm_zero, div_zero, sub_zero, norm_zero], apply Hε},
    {rewrite [norm_zero, div_zero],
    apply and.right Hδ,
    repeat assumption}
  end

theorem is_bdd_linear_map_of_eq {A B : V → W} [HA : is_bdd_linear_map A] (HAB : A = B) :
        is_bdd_linear_map B :=
  begin
    fapply is_bdd_linear_map.mk,
    all_goals try rewrite -HAB,
    {apply hom_add},
    {apply hom_smul},
    {exact op_norm A},
    {exact op_norm_pos A},
    {rewrite -HAB, apply op_norm_bound}
  end

definition is_frechet_deriv_at_of_eq {f A : V → W} [is_bdd_linear_map A] {x : V}
           (Hfd : has_frechet_deriv_at f A x) {B : V → W} (HAB : A = B) :
           @has_frechet_deriv_at _ _ _ _ f B (is_bdd_linear_map_of_eq HAB) x :=
  begin
    unfold has_frechet_deriv_at,
    rewrite -HAB,
    apply Hfd
  end


theorem has_frechet_deriv_at_intro {f A : V → W} [is_bdd_linear_map A] {x : V}
        (H : ∀ ⦃ε : ℝ⦄, ε > 0 →
              (∃ δ : ℝ, δ > 0 ∧ ∀ ⦃x' : V⦄, x' ≠ 0 ∧ ∥x'∥ < δ → ∥f (x + x') - f x - A x'∥ / ∥x'∥ < ε)) :
        has_frechet_deriv_at f A x :=
  begin
    apply normed_vector_space.approaches_at_intro,
    intros ε Hε,
    cases H Hε with δ Hδ,
    cases Hδ with Hδ Hδ',
    existsi δ,
    split,
    assumption,
    intros x' Hx'1 Hx'2,
    show abs (∥f (x + x') - f x - A x'∥ / ∥x'∥ - 0) < ε, begin
      have H : ∥f (x + x') - f x - A x'∥ / ∥x'∥ ≥ 0,
        from div_nonneg_of_nonneg_of_nonneg !norm_nonneg !norm_nonneg,
      rewrite [sub_zero, abs_of_nonneg H],
      apply Hδ',
      split,
      assumption,
      rewrite [-sub_zero x'],
      apply Hx'1
    end
  end

theorem has_frechet_deriv_at_elim {f A : V → W} [is_bdd_linear_map A] {x : V} (H : has_frechet_deriv_at f A x) :
         ∀ ⦃ε : ℝ⦄, ε > 0 →
              (∃ δ : ℝ, δ > 0 ∧ ∀ ⦃x' : V⦄, x' ≠ 0 ∧ ∥x'∥ < δ → ∥f (x + x') - f x - A x'∥ / ∥x'∥ < ε) :=
  begin
    intros ε Hε,
    cases normed_vector_space.approaches_at_dest H Hε with δ Hδ,
    cases Hδ with Hδ Hδ',
    existsi δ,
    split,
    assumption,
    intros x' Hx',
    rewrite [-sub_zero x' at Hx' {2}],
    have Hδ'' : abs (∥f (x + x') - f x - A x'∥ / ∥x'∥ - 0) < ε, from Hδ' (and.right Hx') (and.left Hx'),
    have Hpos : ∥f (x + x') - f x - A x'∥ / ∥x'∥ ≥ 0, from div_nonneg_of_nonneg_of_nonneg !norm_nonneg !norm_nonneg,
    rewrite [sub_zero at Hδ'', abs_of_nonneg Hpos at Hδ''],
    assumption
  end

structure frechet_diffable_at [class] (f : V → W) (x : V) :=
  (A : V → W) [HA : is_bdd_linear_map A] (is_fr_der : has_frechet_deriv_at f A x)

variables f g : V → W
variable x : V

definition frechet_deriv_at [Hf : frechet_diffable_at f x] : V → W :=
  frechet_diffable_at.A _ _ f x

definition frechet_deriv_at_is_bdd_linear_map [instance] (f : V → W) (x : V) [Hf : frechet_diffable_at f x] :
           is_bdd_linear_map (frechet_deriv_at f x) :=
  frechet_diffable_at.HA _ _ f x

theorem frechet_deriv_spec [Hf : frechet_diffable_at f x] :
        (λ h : V, ∥f (x + h) - f x - (frechet_deriv_at f x h) ∥ / ∥ h ∥) ⟶ 0 [at 0] :=
  frechet_diffable_at.is_fr_der _ _ f x

theorem has_frechet_deriv_at_const (w : W) : has_frechet_deriv_at (λ v : V, w) (λ v : V, 0) x :=
  begin
    apply normed_vector_space.approaches_at_intro,
    intros ε Hε,
    existsi 1,
    split,
    exact zero_lt_one,
    intros x' Hx' _,
    rewrite [2 sub_self, norm_zero],
    krewrite [zero_div, sub_zero, norm_zero],
    assumption
  end

theorem has_frechet_deriv_at_id : has_frechet_deriv_at (λ v : V, v) (λ v : V, v) x :=
  begin
    apply normed_vector_space.approaches_at_intro,
    intros ε Hε,
    existsi 1,
    split,
    exact zero_lt_one,
    intros x' Hx' _,
    have x + x' - x - x' = 0, by simp,
    rewrite [this, norm_zero, zero_div, sub_self, norm_zero],
    exact Hε
  end

theorem has_frechet_deriv_at_smul (c : ℝ) {A : V → W} [is_bdd_linear_map A]
        (Hf : has_frechet_deriv_at f A x) : has_frechet_deriv_at (λ y, c • f y) (λ y, c • A y) x :=
  begin
    eapply @decidable.cases_on (abs c = 0),
    exact _,
    {intro Hc,
    have Hz : c = 0, from eq_zero_of_abs_eq_zero Hc,
    have Hfz : (λ y : V, (0 : ℝ) • f y) = (λ y : V, 0), from funext (λ y, !zero_smul),
    --have Hfz' : (λ x : V, (0 : ℝ) • A x) = (λ x : V, 0), from funext (λ y, !zero_smul),
    -- rewriting Hfz' produces type-incorrect term
    rewrite [Hz, Hfz],
    apply metric_space.approaches_at_intro,
    intro ε Hε,
    existsi 1,
    split,
    exact zero_lt_one,
    intro x' Hx' _,
    rewrite [zero_smul, *sub_zero, norm_zero],
    krewrite [zero_div, dist_self],
    exact Hε},
    intro Hcnz,
    apply normed_vector_space.approaches_at_intro,
    intros ε Hε,
    have Hεc : ε / abs c > 0, from div_pos_of_pos_of_pos Hε (lt_of_le_of_ne !abs_nonneg (ne.symm Hcnz)),
    cases normed_vector_space.approaches_at_dest Hf Hεc with δ Hδ,
    cases Hδ with Hδp Hδ,
    existsi δ,
    split,
    assumption,
    intro x' Hx' _,
    show abs ((∥c • f (x + x') - c • f x - c • A x'∥ / ∥x'∥ - 0)) < ε, begin
      rewrite [sub_zero, -2 smul_sub_left_distrib, norm_smul],
      krewrite mul_div_assoc,
      rewrite [abs_mul, abs_abs, -{ε}mul_div_cancel' Hcnz],
      apply mul_lt_mul_of_pos_left,
      have Hδ' : abs (∥f (x + x') - f x - A x'∥ / ∥x'∥ - 0) < ε / abs c, from Hδ Hx' a,
      rewrite sub_zero at Hδ',
      apply Hδ',
      apply lt_of_le_of_ne,
      apply abs_nonneg,
      apply ne.symm,
      apply Hcnz
    end
  end

theorem has_frechet_deriv_at_neg {A : V → W} [is_bdd_linear_map A]
        (Hf : has_frechet_deriv_at f A x) : has_frechet_deriv_at (λ y, - f y) (λ y, - A y) x :=
  begin
    apply has_frechet_deriv_at_intro,
    intros ε Hε,
    cases has_frechet_deriv_at_elim Hf Hε with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro x' Hx',
    rewrite [-norm_neg, neg_sub, sub_neg_eq_add, sub_add_eq_sub_sub, sub_neg_eq_add,
             add_sub_assoc, add.comm, -sub_eq_add_neg],
    apply and.right Hδ,
    assumption
  end

theorem has_frechet_deriv_at_add (A B : V → W) [is_bdd_linear_map A] [is_bdd_linear_map B]
        (Hf : has_frechet_deriv_at f A x) (Hg : has_frechet_deriv_at g B x) :
        has_frechet_deriv_at (λ y, f y + g y) (λ y, A y + B y) x :=
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
    have Hlimge : (λ h, ∥f (x + h) - f x - A h∥ / ∥h∥ + ∥g (x + h) - g x - B h∥ / ∥h∥) ⟶ 0 [at 0], begin
      rewrite [-zero_add 0],
      apply add_approaches,
      apply Hf,
      apply Hg
    end,
    have Hlimle : (λ (h : V), (0 : ℝ)) ⟶ 0 [at 0], by apply approaches_constant,
    apply approaches_squeeze Hlimle Hlimge,
    apply filter.eventually_of_forall,
    intro y,
    apply div_nonneg_of_nonneg_of_nonneg,
    repeat apply norm_nonneg,
    apply filter.eventually_of_forall,
    apply Hle
  end

open topology

theorem continuous_at_of_diffable_at [Hf : frechet_diffable_at f x] : continuous_at f x :=
  begin
    apply normed_vector_space.continuous_at_intro,
    intros ε Hε,
    note Hfds := normed_vector_space.approaches_at_dest (frechet_deriv_spec f x) Hε,
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
    have Hx'x : x' - x ≠ 0 ∧ ∥(x' - x) - 0∥ < δ, from and.intro Hneq begin
      rewrite sub_zero,
      apply lt_of_lt_of_le,
      apply Hx',
      apply min_le_left
    end,
    have Hx'xp : ∥x' - x∥ > 0, from norm_pos_of_ne_zero Hneq,
    have Hδ'' : abs (∥f (x + (x' - x)) - f x - frechet_deriv_at f x (x' - x)∥ / ∥x' - x∥ - 0) < ε,
      from Hδ' (and.right Hx'x) (and.left Hx'x),
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

theorem continuous_at_of_has_frechet_deriv_at {A : V → W} [is_bdd_linear_map A]
        (H : has_frechet_deriv_at f A x) : continuous_at f x :=
  begin
    apply @continuous_at_of_diffable_at,
    existsi A,
    exact H
  end

end frechet_deriv

section comp

lemma div_mul_div_cancel {A : Type} [field A] (a b : A) {c : A} (Hc : c ≠ 0) : (a / c) * (c / b) = a / b :=
  by rewrite [-mul_div_assoc, div_mul_cancel _ Hc]

lemma div_add_eq_add_mul_div {A : Type} [field A] (a b c : A) (Hb : b ≠ 0) : (a / b) + c = (a + c * b) / b :=
  by rewrite [-div_add_div_same, mul_div_cancel _ Hb]

-- I'm not sure why smul_approaches doesn't unify where I use this?
private lemma real_limit_helper {U : Type} [normed_vector_space U] {f : U → ℝ} {a : ℝ} {x : U}
      (Hf : f ⟶ a [at x]) (c : ℝ) : (λ y, c * f y) ⟶ c * a [at x] :=
  begin
    apply smul_approaches,
    exact Hf
  end

variables {U V W : Type}
variables [HU : normed_vector_space U] [HV : normed_vector_space V] [HW : normed_vector_space W]
variables {f : V → W} {g : U → V}
variables {A : V → W} {B : U → V}
variables [HA : is_bdd_linear_map A] [HB : is_bdd_linear_map B]
variable {x : U}

include HU HV HW HA HB

-- this takes 2 seconds without clearing the contexts before simp
theorem has_frechet_deriv_at_comp (Hg : has_frechet_deriv_at g B x) (Hf : has_frechet_deriv_at f A (g x)) :
        @has_frechet_deriv_at _ _ _ _ (λ y, f (g y)) (λ y, A (B y)) !is_bdd_linear_map_comp x :=
  begin
    unfold has_frechet_deriv_at,
    note Hf' := has_frechet_deriv_at_elim Hf,
    note Hg' := has_frechet_deriv_at_elim Hg,
    have H : ∀ h, f (g (x + h)) - f (g x) - A (B h) =
             (A (g (x + h) - g x - B h)) + (-f (g x) + f (g (x + h)) + A (g x - g (x + h))),
      begin intro; rewrite [3 hom_sub A], clear [Hf, Hg, Hf', Hg'], simp end, -- .5 seconds for simp
    have H' : (λ h, ∥f (g (x + h)) - f (g x) - A (B h)∥ / ∥h∥) =
              (λ h, ∥(A (g (x + h) - g x - B h)) + (-f (g x) + f (g (x + h)) + A (g x - g (x + h)))∥ / ∥h∥),
      from funext (λ h, by rewrite H),
    rewrite H',
    clear [H, H'],
    apply approaches_squeeze, -- show the limit holds by bounding it by something that vanishes
    {apply approaches_constant},
    rotate 1,
    {apply filter.eventually_of_forall, intro, apply div_nonneg_of_nonneg_of_nonneg, repeat apply norm_nonneg},
    {apply filter.eventually_of_forall, intro,
    apply div_le_div_of_le_of_nonneg,
    apply norm_triangle,
    apply norm_nonneg},
    have H : (λ (y : U), (∥A (g (x + y) - g x - B y)∥ + ∥-f (g x) + f (g (x + y)) + A (g x - g (x + y))∥) / ∥y∥) =
      (λ (y : U), (∥A (g (x + y) - g x - B y)∥ / ∥y∥ + ∥-f (g x) + f (g (x + y)) + A (g x - g (x + y))∥ / ∥y∥)),
      from funext (λ y, by rewrite [div_add_div_same]),
    rewrite [H, -zero_add 0], -- the function is a sum of two things that both vanish
    clear H,
    apply add_approaches,
    {apply approaches_squeeze, -- show the lhs vanishes by squeezing it again
    {apply approaches_constant},
    rotate 1,
    {apply filter.eventually_of_forall, intro, apply div_nonneg_of_nonneg_of_nonneg, repeat apply norm_nonneg},
    {apply filter.eventually_of_forall, intro y,
    show ∥A (g (x + y) - g x - B y)∥ / ∥y∥ ≤ op_norm A * (∥(g (x + y) - g x - B y)∥ / ∥y∥), begin
      rewrite -mul_div_assoc,
      apply div_le_div_of_le_of_nonneg,
      apply op_norm_bound A,
      apply norm_nonneg
    end},
    {rewrite [-mul_zero (op_norm A)],
    apply real_limit_helper,
    apply Hg}}, -- we have shown the lhs vanishes. now the rhs
    {have H : ∀ y, (∥-f (g x) + f (g (x + y)) + A (g x - g (x + y))∥ / ∥y∥) =
      ((∥(f (g (x + y)) - f (g x)) - A (g (x + y) - g x) ∥ / ∥g (x + y) - g x∥) * (∥g (x + y) - g x∥ / ∥y∥)),
    begin
      intro,
      cases em (g (x + y) - g x = 0) with Heq Hneq,
      {note Heq' := eq_of_sub_eq_zero Heq,
      rewrite [Heq', neg_add_eq_sub, *sub_self, hom_zero A, add_zero, *norm_zero, div_zero, zero_div]},
      {rewrite [div_mul_div_cancel _ _ (norm_ne_zero_of_ne_zero Hneq), *sub_eq_add_neg,
        -hom_neg A],
      clear [Hf, Hg, Hf', Hg', Hneq],
      simp} --(.5 seconds)
    end,
    apply approaches_squeeze, -- again, by squeezing
    {apply approaches_constant},
    rotate 1,
    {apply filter.eventually_of_forall, intro, apply div_nonneg_of_nonneg_of_nonneg, repeat apply norm_nonneg},
    {apply filter.eventually_of_forall, intro y, rewrite H,
    apply mul_le_mul_of_nonneg_left,
    {show ∥g (x + y) - g x∥ / ∥y∥ ≤  ∥g (x + y) - g x - B y∥ / ∥y∥ + op_norm B, begin
      cases em (y = 0) with Heq Hneq,
      {rewrite [Heq, norm_zero, *div_zero, zero_add], apply le_of_lt, apply op_norm_pos},
      rewrite [div_add_eq_add_mul_div _ _ _ (norm_ne_zero_of_ne_zero Hneq)],
      apply div_le_div_of_le_of_nonneg,
      apply le.trans,
      rotate 1,
      apply add_le_add_left,
      apply op_norm_bound,
      apply norm_nonneg,
      rewrite [-neg_add_cancel_right (g (x + y) - g x) (B y) at {1}, -sub_eq_add_neg],
      apply norm_triangle
    end},
    {apply div_nonneg_of_nonneg_of_nonneg, repeat apply norm_nonneg}},
    -- now to show the bounding function vanishes. it is a product of a vanishing function and a convergent one
    apply mul_approaches_zero_of_approaches_zero_of_approaches,
    {have H' : (λ (y : U), ∥f (g (x + y)) - f (g x) - A (g (x + y) - g x)∥ / ∥g (x + y) - g x∥) =
            (λ (y : U), ∥f (g x + (g (x + y) - g x)) - f (g x) - A (g (x + y) - g x)∥ / ∥g (x + y) - g x∥),
      from funext (λ y, by rewrite [add.comm (g x), sub_add_cancel]), -- first, show lhs vanishes
    rewrite H',
    have Hgcts : continuous_at (λ y, g (x + y) - g x) 0, begin
      apply normed_vector_space.continuous_at_intro,
      intro ε Hε,
      cases normed_vector_space.continuous_at_dest (continuous_at_of_has_frechet_deriv_at g x Hg) _ Hε with δ Hδ,
      existsi δ,
      split,
      exact and.left Hδ,
      intro x' Hx',
      rewrite [add_zero, sub_self],
      rewrite sub_zero,
      apply and.right Hδ,
      have (x + x') - x = x' - 0, begin clear [Hg, Hf, Hf', Hg', H, H', Hδ, Hx'], simp end, -- (.6 seconds w/o clear, .1 with)
      rewrite this,
      apply Hx'
    end,
    have Hfcts : continuous_at (λ (x' : V), ∥f (g x + x') - f (g x) - A x'∥ / ∥x'∥) (g (x + 0) - g x), begin
      rewrite [add_zero, sub_self],
      apply diff_quot_cts,
      exact Hf
    end,
    have Heqz : ∥f (g x + (g (x + 0) - g x)) - f (g x) - A (g (x + 0) - g x)∥ / ∥g (x + 0) - g x∥ = 0,
      by rewrite [*add_zero, sub_self, norm_zero, div_zero],
    apply @tendsto_comp _ _ _ (λ y, g (x + y) - g x),
    apply tendsto_inf_left,
    apply tendsto_at_of_continuous_at Hgcts,
    note Hfcts' := tendsto_at_of_continuous_at Hfcts,
    rewrite Heqz at Hfcts',
    exact Hfcts'}, -- finally, show rhs converges to op_norm B
    {apply add_approaches,
    apply Hg,
    apply approaches_constant}}
  end

end comp

end analysis
