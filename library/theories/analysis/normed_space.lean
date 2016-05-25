/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Normed spaces.
-/
import algebra.module .metric_space
open real nat classical topology analysis analysis.metric_space
noncomputable theory

structure has_norm [class] (M : Type) : Type :=
(norm : M → ℝ)

namespace analysis
  definition norm {M : Type} [has_normM : has_norm M] (v : M) : ℝ := has_norm.norm v

  notation `∥`v`∥` := norm v
end analysis

/- real vector spaces -/
-- where is the right place to put this?
structure real_vector_space [class] (V : Type) extends vector_space ℝ V

section
  variables {V : Type} [real_vector_space V]

  -- these specializations help the elaborator when it is hard to infer the ring, e.g. with numerals

  proposition smul_left_distrib_real (a : ℝ) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_left_distrib a u v

  proposition smul_right_distrib_real (a b : ℝ) (u : V) : (a + b) • u = a • u + b • u :=
  smul_right_distrib a b u

  proposition mul_smul_real (a : ℝ) (b : ℝ) (u : V) : (a * b) • u = a • (b • u) :=
  mul_smul a b u

  proposition one_smul_real (u : V) : (1 : ℝ) • u = u := one_smul u

  proposition zero_smul_real (u : V) : (0 : ℝ) • u = 0 := zero_smul u

  proposition smul_zero_real (a : ℝ) : a • (0 : V) = 0 := smul_zero a

  proposition neg_smul_real (a : ℝ) (u : V) : (-a) • u = - (a • u) := neg_smul a u

  proposition neg_one_smul_real (u : V) : -(1 : ℝ) • u = -u := neg_one_smul u

  proposition smul_neg_real (a : ℝ) (u : V) : a • (-u) = -(a • u) := smul_neg a u
end

/- real normed vector spaces -/

structure normed_vector_space [class] (V : Type) extends real_vector_space V, has_norm V :=
(norm_zero : norm zero = 0)
(eq_zero_of_norm_eq_zero : ∀ u : V, norm u = 0 → u = zero)
(norm_triangle : ∀ u v, norm (add u v) ≤ norm u + norm v)
(norm_smul : ∀ (a : ℝ) (v : V), norm (smul a v) = abs a * norm v)

namespace analysis
  variable {V : Type}
  variable [normed_vector_space V]

  proposition norm_zero : ∥ (0 : V) ∥ = 0 := !normed_vector_space.norm_zero

  proposition eq_zero_of_norm_eq_zero {u : V} (H : ∥ u ∥ = 0) : u = 0 :=
  !normed_vector_space.eq_zero_of_norm_eq_zero H

  proposition norm_triangle (u v : V) : ∥ u + v ∥ ≤ ∥ u ∥ + ∥ v ∥ :=
  !normed_vector_space.norm_triangle

  proposition norm_smul (a : ℝ) (v : V) : ∥ a • v ∥ = abs a * ∥ v ∥ :=
  !normed_vector_space.norm_smul

  proposition norm_neg (v : V) : ∥ -v ∥ = ∥ v ∥ :=
  have abs (1 : ℝ) = 1, from abs_of_nonneg zero_le_one,
  by rewrite [-@neg_one_smul ℝ V, norm_smul, abs_neg, this, one_mul]

  proposition norm_sub (u v : V) : ∥u - v∥ = ∥v - u∥ :=
    by rewrite [-norm_neg, neg_sub]

  proposition norm_ne_zero_of_ne_zero {u : V} (H : u ≠ 0) : ∥u∥ ≠ 0 :=
  suppose ∥u∥ = 0, H (eq_zero_of_norm_eq_zero this)

end analysis

section
  open analysis
  variable {V : Type}
  variable [normed_vector_space V]

  private definition nvs_dist [reducible] (u v : V) := ∥ u - v ∥

  private lemma nvs_dist_self (u : V) : nvs_dist u u = 0 :=
  by rewrite [↑nvs_dist, sub_self, norm_zero]

  private lemma eq_of_nvs_dist_eq_zero (u v : V) (H : nvs_dist u v = 0) : u = v :=
  have u - v = 0, from eq_zero_of_norm_eq_zero H,
  eq_of_sub_eq_zero this

  private lemma nvs_dist_triangle (u v w : V) : nvs_dist u w ≤ nvs_dist u v + nvs_dist v w :=
  calc
    nvs_dist u w = ∥ (u - v) + (v - w) ∥       : by rewrite [↑nvs_dist, *sub_eq_add_neg, add.assoc,
                                                             neg_add_cancel_left]
             ... ≤ ∥ u - v ∥ + ∥ v - w ∥       : norm_triangle
  private lemma nvs_dist_comm  (u v : V) : nvs_dist u v = nvs_dist v u :=
  by rewrite [↑nvs_dist, -norm_neg, neg_sub]

  definition normed_vector_space_to_metric_space [trans_instance]
      (V : Type) [nvsV : normed_vector_space V] :
    metric_space V :=
  ⦃ metric_space,
    dist               := nvs_dist,
    dist_self          := nvs_dist_self,
    eq_of_dist_eq_zero := eq_of_nvs_dist_eq_zero,
    dist_comm          := nvs_dist_comm,
    dist_triangle      := nvs_dist_triangle
  ⦄

  open nat

  proposition approaches_seq_norm_elim {X : ℕ → V} {x : V} (H : X ⟶ x [at ∞]) :
    ∀ {ε : ℝ}, ε > 0 → ∃ N₁ : ℕ, ∀ {n : ℕ}, n ≥ N₁ → ∥ X n - x ∥ < ε :=
  approaches_at_infty_dest H

  proposition dist_eq_norm_sub (u v : V) : dist u v = ∥ u - v ∥ := rfl

  proposition norm_eq_dist_zero (u : V) : ∥ u ∥ = dist u 0 :=
  by rewrite [dist_eq_norm_sub, sub_zero]

  proposition norm_nonneg (u : V) : ∥ u ∥ ≥ 0 :=
  by rewrite norm_eq_dist_zero; apply !dist_nonneg

  proposition norm_pos_of_ne_zero {v : V} (Hv : v ≠ 0) : ∥v∥ > 0 :=
    by_contradiction
      (suppose ¬ ∥v∥ > 0,
      have ∥v∥ = 0, from eq_of_le_of_ge (le_of_not_gt this) !norm_nonneg,
      Hv (eq_zero_of_norm_eq_zero this))
end

structure banach_space [class] (V : Type) extends nvsV : normed_vector_space V :=
(complete : ∀ X, @analysis.cauchy V (@normed_vector_space_to_metric_space V nvsV) X →
    @analysis.converges_seq V (@normed_vector_space_to_metric_space V nvsV) X)

definition banach_space_to_metric_space [trans_instance] (V : Type) [bsV : banach_space V] :
  complete_metric_space V :=
⦃ complete_metric_space, normed_vector_space_to_metric_space V,
  complete := banach_space.complete
⦄

namespace analysis

-- unfold some common definitions fully (copied from metric space, updated for normed_space notation)
-- TODO: copy these for ℝ as well?
namespace normed_vector_space
section
open set topology set.filter
variables {M N : Type}
--variable [HU : normed_vector_space U]
variable [normed_vector_space M]
--variables {f g : U → V}

section approaches
  variables {X : Type} {F : filter X} {f : X → M} {y : M}

  proposition approaches_intro (H : ∀ ε, ε > 0 → eventually (λ x, ∥(f x) - y∥ < ε) F) :
    (f ⟶ y) F :=
  approaches_intro H

  proposition approaches_dest (H : (f ⟶ y) F) {ε : ℝ} (εpos : ε > 0) :
    eventually (λ x, ∥(f x) - y∥ < ε) F :=
  approaches_dest H εpos

  variables (F f y)

  proposition approaches_iff : ((f ⟶ y) F) ↔ (∀ ε, ε > 0 → eventually (λ x, ∥(f x) - y∥ < ε) F) :=
  iff.intro approaches_dest approaches_intro

end approaches

proposition approaches_at_infty_intro {f : ℕ → M} {y : M}
    (H : ∀ ε, ε > 0 → ∃ N, ∀ n, n ≥ N → ∥(f n) - y∥ < ε) :
  f ⟶ y [at ∞] :=
approaches_at_infty_intro H

proposition approaches_at_infty_dest {f : ℕ → M} {y : M}
    (H : f ⟶ y [at ∞]) ⦃ε : ℝ⦄ (εpos : ε > 0) :
  ∃ N, ∀ ⦃n⦄, n ≥ N → ∥(f n) - y∥ < ε :=
approaches_at_infty_dest H εpos

proposition approaches_at_infty_iff (f : ℕ → M) (y : M) :
  f ⟶ y [at ∞] ↔ (∀ ε, ε > 0 → ∃ N, ∀ ⦃n⦄, n ≥ N → ∥(f n) - y∥ < ε) :=
iff.intro approaches_at_infty_dest approaches_at_infty_intro

variable [normed_vector_space N]

proposition approaches_at_dest {f : M → N} {y : N} {x : M}
    (H : f ⟶ y [at x]) ⦃ε : ℝ⦄ (εpos : ε > 0) :
  ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, ∥x' - x∥ < δ → x' ≠ x → ∥(f x') - y∥ < ε :=
approaches_at_dest H εpos

proposition approaches_at_intro {f : M → N} {y : N} {x : M}
    (H : ∀ ε, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, ∥x' - x∥ < δ → x' ≠ x → ∥(f x') - y∥ < ε) :
  f ⟶ y [at x] :=
approaches_at_intro H

proposition approaches_at_iff (f : M → N) (y : N) (x : M) : f ⟶ y [at x] ↔
    (∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, ∥x' - x∥ < δ → x' ≠ x → ∥(f x') - y∥ < ε) :=
iff.intro approaches_at_dest approaches_at_intro

end
end normed_vector_space


section
variable {V : Type}
variable [normed_vector_space V]
variable {A : Type}
variables {X : A → V}
variables {x : V}

proposition neg_approaches {F} (HX : (X ⟶ x) F) :
  ((λ n, - X n) ⟶ - x) F :=
  begin
    apply normed_vector_space.approaches_intro,
    intro ε Hε,
    apply set.filter.eventually_mono (approaches_dest HX Hε),
    intro x' Hx',
    rewrite [-norm_neg, neg_neg_sub_neg],
    apply Hx'
  end

proposition approaches_neg {F} (Hx : ((λ n, - X n) ⟶ - x) F) : (X ⟶ x) F :=
  have aux : X = λ n, (- (- X n)), from funext (take n, by rewrite neg_neg),
  by rewrite [aux, -neg_neg x]; exact neg_approaches Hx

proposition neg_approaches_iff {F} : (((λ n, - X n) ⟶ - x) F) ↔ ((X ⟶ x) F) :=
have aux : X = λ n, (- (- X n)), from funext (take n, by rewrite neg_neg),
iff.intro approaches_neg neg_approaches

proposition norm_approaches_zero_of_approaches_zero {F} (HX : (X ⟶ 0) F) : ((λ n, norm (X n)) ⟶ 0) F :=
  begin
    apply metric_space.approaches_intro,
    intro ε Hε,
    apply set.filter.eventually_mono (approaches_dest HX Hε),
    intro x Hx,
    change abs (∥X x∥ - 0) < ε,
    rewrite [sub_zero, abs_of_nonneg !norm_nonneg, -sub_zero (X x)],
    apply Hx
  end

proposition approaches_zero_of_norm_approaches_zero
    {F} (HX : ((λ n, norm (X n)) ⟶ 0) F) :
  (X ⟶ 0) F :=
  begin
    apply normed_vector_space.approaches_intro,
    intro ε Hε,
    apply set.filter.eventually_mono (approaches_dest HX Hε),
    intro x Hx,
    apply lt_of_abs_lt,
    rewrite [sub_zero, -sub_zero ∥X x∥],
    apply Hx
  end

proposition norm_approaches_zero_iff (X : ℕ → V) (F) :
  (((λ n, norm (X n)) ⟶ 0) F) ↔ ((X ⟶ 0) F) :=
iff.intro approaches_zero_of_norm_approaches_zero norm_approaches_zero_of_approaches_zero

end


section
variables {U V : Type}
--variable [HU : normed_vector_space U]
variable [HV : normed_vector_space V]
variables {f g : U → V}
open set-- filter causes error??
include  HV

theorem add_approaches {lf lg : V} {F : filter U} (Hf : (f ⟶ lf) F) (Hg : (g ⟶ lg) F) :
        ((λ y, f y + g y) ⟶ lf + lg) F :=
  begin
    apply normed_vector_space.approaches_intro,
    intro ε Hε,
    have e2pos : ε / 2 > 0, from div_pos_of_pos_of_pos Hε two_pos,
    have Hfl : filter.eventually (λ x, dist (f x) lf < ε / 2) F, from approaches_dest Hf e2pos,
    have Hgl : filter.eventually (λ x, dist (g x) lg < ε / 2) F, from approaches_dest Hg e2pos,
    apply filter.eventually_mono,
    apply filter.eventually_and Hfl Hgl,
    intro x Hfg,
    rewrite [add_sub_comm, -add_halves ε],
    apply lt_of_le_of_lt,
    apply norm_triangle,
    cases Hfg with Hf' Hg',
    apply add_lt_add,
    exact Hf', exact Hg'
  end

theorem smul_approaches {lf : V} {F : filter U} (Hf : (f ⟶ lf) F) (s : ℝ) :
        ((λ y, s • f y) ⟶ s • lf) F :=
  begin
    apply normed_vector_space.approaches_intro,
    intro ε Hε,
    cases em (s = 0) with seq sneq,
    {have H : (λ x, ∥(s • f x) - (s • lf)∥ < ε) = (λ x, true),
      begin apply funext, intro x, rewrite [seq, 2 zero_smul, sub_zero, norm_zero, eq_true], exact Hε end,
    rewrite H,
    apply filter.eventually_true},
    {have e2pos : ε / abs s > 0, from div_pos_of_pos_of_pos Hε (abs_pos_of_ne_zero sneq),
    have H : filter.eventually (λ x, ∥(f x) - lf∥ < ε / abs s) F, from approaches_dest Hf e2pos,
    apply filter.eventually_mono H,
    intro x Hx,
    rewrite [-smul_sub_left_distrib, norm_smul, mul.comm],
    apply mul_lt_of_lt_div,
    apply abs_pos_of_ne_zero sneq,
    apply Hx}
  end

end

namespace normed_vector_space
variables {U V : Type}
variables [HU : normed_vector_space U] [HV : normed_vector_space V]
variables {f g : U → V}
include HU HV
open set

theorem continuous_at_within_intro {x : U} {s : set U}
        (H : ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → ∥x' - x∥ < δ → ∥(f x') - (f x)∥ < ε) :
  continuous_at_on f x s :=
  metric_space.continuous_at_within_intro H

theorem continuous_at_on_dest {x : U} {s : set U} (Hfx : continuous_at_on f x s) :
         ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → ∥x' - x∥ < δ → ∥(f x') - (f x)∥ < ε :=
  metric_space.continuous_at_on_dest Hfx

theorem continuous_on_intro {s : set U}
        (H : ∀ x ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → ∥x' - x∥ < δ → ∥(f x') - (f x)∥ < ε) :
        continuous_on f s :=
  metric_space.continuous_on_intro H

theorem continuous_on_dest {s : set U} (H : continuous_on f s) {x : U} (Hxs : x ∈ s) :
        ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → ∥x' - x∥ < δ → ∥(f x') - (f x)∥ < ε :=
  metric_space.continuous_on_dest H Hxs

theorem continuous_intro
        (H : ∀ x ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, ∥x' - x∥ < δ → ∥(f x') - (f x)∥ < ε) :
        continuous f :=
  metric_space.continuous_intro H

theorem continuous_dest (H : continuous f) (x : U) :
         ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, ∥x' - x∥ < δ → ∥(f x') - (f x)∥ < ε :=
  metric_space.continuous_dest H x

theorem continuous_at_intro {x : U}
        (H : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ ∀ x' : U, ∥x' - x∥ < δ → ∥f x' - f x∥ < ε)) :
        continuous_at f x :=
  metric_space.continuous_at_intro H

theorem continuous_at_dest {x : U} (H : continuous_at f x) :
         ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ ∀ x' : U, ∥x' - x∥ < δ → ∥f x' - f x∥ < ε) :=
  metric_space.continuous_at_dest H

end normed_vector_space

section

open topology
variables {U V : Type}
variables [HU : normed_vector_space U] [HV : normed_vector_space V]
variables {f g : U → V}
include HU HV

theorem neg_continuous (Hf : continuous f) : continuous (λ x : U, - f x) :=
  begin
    apply continuous_of_forall_continuous_at,
    intro x,
    apply continuous_at_of_tendsto_at,
    apply neg_approaches,
    apply tendsto_at_of_continuous_at,
    apply forall_continuous_at_of_continuous,
    apply Hf
  end

theorem add_continuous (Hf : continuous f) (Hg : continuous g) : continuous (λ x, f x + g x) :=
  begin
    apply continuous_of_forall_continuous_at,
    intro y,
    apply continuous_at_of_tendsto_at,
    apply add_approaches,
    all_goals apply tendsto_at_of_continuous_at,
    all_goals apply forall_continuous_at_of_continuous,
    repeat assumption
  end

theorem sub_continuous (Hf : continuous f) (Hg : continuous g) : continuous (λ x, f x - g x) :=
  begin
    apply continuous_of_forall_continuous_at,
    intro y,
    apply continuous_at_of_tendsto_at,
    apply add_approaches,
    all_goals apply tendsto_at_of_continuous_at,
    all_goals apply forall_continuous_at_of_continuous,
    assumption,
    apply neg_continuous,
    assumption
  end

theorem smul_continuous (s : ℝ) (Hf : continuous f) : continuous (λ x : U, s • f x) :=
  begin
    apply continuous_of_forall_continuous_at,
    intro y,
    apply continuous_at_of_tendsto_at,
    apply smul_approaches,
    apply tendsto_at_of_continuous_at,
    apply forall_continuous_at_of_continuous,
    assumption
  end

end

end analysis
