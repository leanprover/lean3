/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis

Instantiates the reals as a Banach space.
-/
import .metric_space data.real.complete data.set .normed_space
open real classical analysis nat topology
noncomputable theory

/- sup and inf -/

-- Expresses completeness, sup, and inf in a manner that is less constructive, but more convenient,
-- than the way it is done in data.real.complete.

-- Issue: real.sup and real.inf conflict with sup and inf in lattice.
-- Perhaps put algebra sup and inf into a namespace?

namespace real
open set

private definition exists_is_sup {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b)) :
  ∃ y, is_sup X y :=
let x := some (and.left H), b := some (and.right H) in
  exists_is_sup_of_inh_of_bdd X x (some_spec (and.left H)) b (some_spec (and.right H))

private definition sup_aux {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b)) :=
some (exists_is_sup H)

private definition sup_aux_spec {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b)) :
  is_sup X (sup_aux H) :=
some_spec (exists_is_sup H)

definition sup (X : set ℝ) : ℝ :=
if H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b) then sup_aux H else 0

proposition le_sup {x : ℝ} {X : set ℝ} (Hx : x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → x ≤ b) :
  x ≤ sup X :=
have H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b),
  from and.intro (exists.intro x Hx) (exists.intro b Hb),
by rewrite [↑sup, dif_pos H]; exact and.left (sup_aux_spec H) x Hx

proposition sup_le {X : set ℝ} (HX : ∃ x, x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → x ≤ b) :
  sup X ≤ b :=
have H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b),
  from and.intro HX (exists.intro b Hb),
by rewrite [↑sup, dif_pos H]; exact and.right (sup_aux_spec H) b Hb

proposition exists_mem_and_lt_of_lt_sup {X : set ℝ} (HX : ∃ x, x ∈ X) {b : ℝ} (Hb : b < sup X) :
∃ x, x ∈ X ∧ b < x :=
have ¬ ∀ x, x ∈ X → x ≤ b, from assume H, not_le_of_gt Hb (sup_le HX H),
obtain x (Hx : ¬ (x ∈ X → x ≤ b)), from exists_not_of_not_forall this,
exists.intro x
  (have x ∈ X ∧ ¬ x ≤ b, by rewrite [-not_implies_iff_and_not]; apply Hx,
     and.intro (and.left this) (lt_of_not_ge (and.right this)))

private definition exists_is_inf {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x)) :
  ∃ y, is_inf X y :=
let x := some (and.left H), b := some (and.right H) in
  exists_is_inf_of_inh_of_bdd X x (some_spec (and.left H)) b (some_spec (and.right H))

private definition inf_aux {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x)) :=
some (exists_is_inf H)

private definition inf_aux_spec {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x)) :
  is_inf X (inf_aux H) :=
some_spec (exists_is_inf H)

definition inf (X : set ℝ) : ℝ :=
if H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x) then inf_aux H else 0

proposition inf_le {x : ℝ} {X : set ℝ} (Hx : x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → b ≤ x) :
  inf X ≤ x :=
have H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x),
  from and.intro (exists.intro x Hx) (exists.intro b Hb),
by rewrite [↑inf, dif_pos H]; exact and.left (inf_aux_spec H) x Hx

proposition le_inf {X : set ℝ} (HX : ∃ x, x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → b ≤ x) :
  b ≤ inf X :=
have H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x),
  from and.intro HX (exists.intro b Hb),
by rewrite [↑inf, dif_pos H]; exact and.right (inf_aux_spec H) b Hb

proposition exists_mem_and_lt_of_inf_lt {X : set ℝ} (HX : ∃ x, x ∈ X) {b : ℝ} (Hb : inf X < b) :
∃ x, x ∈ X ∧ x < b :=
have ¬ ∀ x, x ∈ X → b ≤ x, from assume H, not_le_of_gt Hb (le_inf HX H),
obtain x (Hx : ¬ (x ∈ X → b ≤ x)), from exists_not_of_not_forall this,
exists.intro x
  (have x ∈ X ∧ ¬ b ≤ x, by rewrite [-not_implies_iff_and_not]; apply Hx,
     and.intro (and.left this) (lt_of_not_ge (and.right this)))

section
local attribute mem [reducible]
-- TODO: is there a better place to put this?
proposition image_neg_eq (X : set ℝ) : (λ x, -x) ' X = {x | -x ∈ X} :=
set.ext (take x, iff.intro
  (assume H, obtain y [(Hy₁ : y ∈ X) (Hy₂ : -y = x)], from H,
    show -x ∈ X, by rewrite [-Hy₂, neg_neg]; exact Hy₁)
  (assume H : -x ∈ X, exists.intro (-x) (and.intro H !neg_neg)))

proposition sup_neg {X : set ℝ} (nonempty_X : ∃ x, x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → b ≤ x) :
  sup {x | -x ∈ X} = - inf X :=
let negX := {x | -x ∈ X} in
have nonempty_negX : ∃ x, x ∈ negX, from
  obtain x Hx, from nonempty_X,
  have -(-x) ∈ X,
    by rewrite neg_neg; apply Hx,
  exists.intro (-x) this,
have H₁ : ∀ x, x ∈ negX → x ≤ - inf X, from
  take x,
  assume H,
  have inf X ≤ -x,
    from inf_le H Hb,
  show x ≤ - inf X,
    from le_neg_of_le_neg this,
have H₂ : ∀ x, x ∈ X → -sup negX ≤ x, from
  take x,
  assume H,
  have -(-x) ∈ X, by rewrite neg_neg; apply H,
  have -x ≤ sup negX, from le_sup this H₁,
  show -sup negX ≤ x,
    from !neg_le_of_neg_le this,
eq_of_le_of_ge
  (show sup negX ≤ - inf X,
    from sup_le nonempty_negX H₁)
  (show -inf X ≤ sup negX,
    from !neg_le_of_neg_le (le_inf nonempty_X H₂))

proposition inf_neg {X : set ℝ} (nonempty_X : ∃ x, x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → x ≤ b) :
  inf {x | -x ∈ X} = - sup X :=
let negX := {x | -x ∈ X} in
have nonempty_negX : ∃ x, x ∈ negX, from
  obtain x Hx, from nonempty_X,
  have -(-x) ∈ X,
    by rewrite neg_neg; apply Hx,
  exists.intro (-x) this,
have Hb' : ∀ x, x ∈ negX → -b ≤ x,
  from take x, assume H, !neg_le_of_neg_le (Hb _ H),
have HX : X = {x | -x ∈ negX},
  from set.ext (take x, by rewrite [↑set_of, ↑mem, +neg_neg]),
show inf {x | -x ∈ X} = - sup X,
  by rewrite [HX at {2}, sup_neg nonempty_negX Hb', neg_neg]
end
end real

/- the reals form a complete metric space -/

namespace real
proposition approaches_at_infty_intro {X : ℕ → ℝ} {y : ℝ}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) < ε) :
  (X ⟶ y [at ∞]) := metric_space.approaches_at_infty_intro H

proposition approaches_at_infty_dest {X : ℕ → ℝ} {y : ℝ} (H : X ⟶ y [at ∞]) :
    ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) < ε := metric_space.approaches_at_infty_dest H

proposition approaches_at_infty_intro' {X : ℕ → ℝ} {y : ℝ}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) ≤ ε) :
  (X ⟶ y [at ∞]) :=
approaches_at_infty_intro' H
end real

namespace analysis

theorem dist_eq_abs (x y : real) : dist x y = abs (x - y) := rfl

open pnat subtype
local postfix ⁻¹ := pnat.inv

private definition pnat.succ (n : ℕ) : ℕ+ := tag (succ n) !succ_pos

private definition r_seq_of (X : ℕ → ℝ) : r_seq := λ n, X (elt_of n)

private lemma rate_of_cauchy_aux {X : ℕ → ℝ} (H : cauchy X) :
  ∀ k : ℕ+, ∃ N : ℕ+, ∀ m n : ℕ+,
    m ≥ N → n ≥ N → abs (X (elt_of m) - X (elt_of n)) ≤ of_rat k⁻¹ :=
take k : ℕ+,
have H1 : (k⁻¹ >[rat] (rat.of_num 0)), from !pnat.inv_pos,
have H2 : (of_rat k⁻¹ > of_rat (rat.of_num 0)), from !of_rat_lt_of_rat_of_lt H1,
obtain (N : ℕ) (H : ∀ m n, m ≥ N → n ≥ N → abs (X m - X n) < of_rat k⁻¹), from H _ H2,
exists.intro (pnat.succ N)
  (take m n : ℕ+,
    assume Hm : m ≥ (pnat.succ N),
    assume Hn : n ≥ (pnat.succ N),
    have Hm' : elt_of m ≥ N, begin apply le.trans, apply le_succ, apply Hm end,
    have Hn' : elt_of n ≥ N, begin apply le.trans, apply le_succ, apply Hn end,
    show abs (X (elt_of m) - X (elt_of n)) ≤ of_rat k⁻¹, from le_of_lt (H _ _ Hm' Hn'))

private definition rate_of_cauchy {X : ℕ → ℝ} (H : cauchy X) (k : ℕ+) : ℕ+ :=
some (rate_of_cauchy_aux H k)

private lemma cauchy_with_rate_of_cauchy {X : ℕ → ℝ} (H : cauchy X) :
  cauchy_with_rate (r_seq_of X) (rate_of_cauchy H) :=
take k : ℕ+,
some_spec (rate_of_cauchy_aux H k)

private lemma converges_to_with_rate_of_cauchy {X : ℕ → ℝ} (H : cauchy X) :
  ∃ l Nb, converges_to_with_rate (r_seq_of X) l Nb :=
begin
  apply exists.intro,
  apply exists.intro,
  apply converges_to_with_rate_of_cauchy_with_rate,
  exact cauchy_with_rate_of_cauchy H
end

theorem converges_seq_of_cauchy {X : ℕ → ℝ} (H : cauchy X) : converges_seq X :=
obtain l Nb (conv : converges_to_with_rate (r_seq_of X) l Nb),
  from converges_to_with_rate_of_cauchy H,
exists.intro l
  (real.approaches_at_infty_intro
    take ε : ℝ,
    suppose ε > 0,
    obtain (k' : ℕ) (Hn : 1 / succ k' < ε), from archimedean_small `ε > 0`,
    let k : ℕ+ := tag (succ k') !succ_pos,
        N : ℕ+ := Nb k in
    have Hk : real.of_rat k⁻¹ < ε,
      by rewrite [↑pnat.inv, of_rat_divide]; exact Hn,
    exists.intro (elt_of N)
      (take n : ℕ,
        assume Hn : n ≥ elt_of N,
        let n' : ℕ+ := tag n (nat.lt_of_lt_of_le (has_property N) Hn) in
        have abs (X n - l) ≤ real.of_rat k⁻¹, by apply conv k n' Hn,
        show abs (X n - l) < ε, from lt_of_le_of_lt this Hk))

end analysis

definition complete_metric_space_real [trans_instance] :
  complete_metric_space ℝ :=
⦃complete_metric_space, metric_space_real,
  complete := @analysis.converges_seq_of_cauchy
⦄

/- the real numbers can be viewed as a banach space -/

definition real_vector_space_real : real_vector_space ℝ :=
⦃ real_vector_space, real.discrete_linear_ordered_field,
  smul               := mul,
  smul_left_distrib  := left_distrib,
  smul_right_distrib := right_distrib,
  mul_smul           := mul.assoc,
  one_smul           := one_mul
⦄

definition banach_space_real [trans_instance] : banach_space ℝ :=
⦃ banach_space, real_vector_space_real,
  norm                    := abs,
  norm_zero               := abs_zero,
  eq_zero_of_norm_eq_zero := λ a H, eq_zero_of_abs_eq_zero H,
  norm_triangle           := abs_add_le_abs_add_abs,
  norm_smul               := abs_mul,
  complete                := λ X H, analysis.complete ℝ H
⦄

namespace real
open topology set
open normed_vector_space

section
variable {f : ℝ → ℝ}

theorem continuous_dest (H : continuous f) :
  ∀ x : ℝ, ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ,
    abs (x' - x) < δ → abs (f x' - f x) < ε :=
normed_vector_space.continuous_dest H

theorem continuous_intro
  (H : ∀ x : ℝ, ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ,
    abs (x' - x) < δ → abs (f x' - f x) < ε) :
  continuous f :=
normed_vector_space.continuous_intro H

theorem continuous_at_dest {x : ℝ} (H : continuous_at f x) :
         ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ, abs (x' - x) < δ → abs (f x' - f x) < ε) :=
normed_vector_space.continuous_at_dest H

theorem continuous_at_intro {x : ℝ}
  (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ,
    abs (x' - x) < δ → abs (f x' - f x) < ε) :
  continuous_at f x :=
normed_vector_space.continuous_at_intro H

theorem continuous_at_within_intro {x : ℝ} {s : set ℝ}
        (H : ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → abs (x' - x) < δ → abs ((f x') - (f x)) < ε) :
  continuous_at_on f x s :=
normed_vector_space.continuous_at_within_intro H


theorem continuous_at_on_dest {x : ℝ} {s : set ℝ} (Hfx : continuous_at_on f x s) :
         ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → abs (x' - x) < δ → abs ((f x') - (f x)) < ε :=
normed_vector_space.continuous_at_on_dest Hfx

theorem continuous_on_intro {s : set ℝ}
        (H : ∀ x ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → abs (x' - x) < δ → abs ((f x') - (f x)) < ε) :
        continuous_on f s :=
normed_vector_space.continuous_on_intro H

theorem continuous_on_dest {s : set ℝ} (H : continuous_on f s) {x : ℝ} (Hxs : x ∈ s) :
        ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → abs (x' - x) < δ → abs ((f x') - (f x)) < ε :=
normed_vector_space.continuous_on_dest H Hxs

end

section approaches
open set.filter set topology
  variables {X : Type} {F : filter X} {f : X → ℝ} {y : ℝ}

  proposition approaches_intro (H : ∀ ε, ε > 0 → eventually (λ x, abs ((f x) - y) < ε) F) :
    (f ⟶ y) F :=
  normed_vector_space.approaches_intro H

  proposition approaches_dest (H : (f ⟶ y) F) {ε : ℝ} (εpos : ε > 0) :
    eventually (λ x, abs ((f x) - y) < ε) F :=
  normed_vector_space.approaches_dest H εpos

  variables (F f y)

  proposition approaches_iff : ((f ⟶ y) F) ↔ (∀ ε, ε > 0 → eventually (λ x, abs ((f x) - y) < ε) F) :=
  iff.intro approaches_dest approaches_intro

end approaches

section
variable {f : ℝ → ℝ}
proposition approaches_at_dest  {y x : ℝ}
    (H : f ⟶ y [at x]) ⦃ε : ℝ⦄ (εpos : ε > 0) :
  ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, abs (x' - x) < δ → x' ≠ x → abs ((f x') - y) < ε :=
metric_space.approaches_at_dest H εpos

proposition approaches_at_intro {y x : ℝ}
    (H : ∀ ε, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, abs (x' - x) < δ → x' ≠ x → abs ((f x') - y) < ε) :
  f ⟶ y [at x] :=
metric_space.approaches_at_intro H

proposition approaches_at_iff (y x : ℝ) : f ⟶ y [at x] ↔
    (∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, abs (x' - x) < δ → x' ≠ x → abs ((f x') - y) < ε) :=
iff.intro approaches_at_dest approaches_at_intro

end

end real

/- limits under pointwise operations -/

section limit_operations
open set
variable {A : Type}
variables {X Y : A → ℝ}
variables {x y : ℝ}
variable {F : filter A}

proposition mul_left_approaches (c : ℝ) (HX : (X ⟶ x) F) :
  ((λ n, c * X n) ⟶ c * x) F :=
smul_approaches HX c

proposition mul_right_approaches (c : ℝ) (HX : (X ⟶ x) F) :
  ((λ n, X n * c) ⟶ x * c) F :=
have (λ n, X n * c) = (λ n, c * X n), from funext (λ n, !mul.comm),
by rewrite [this, mul.comm]; apply mul_left_approaches _ HX

theorem approaches_squeeze (HX : (X ⟶ x) F) (HY : (Y ⟶ x) F)
        {Z : A → ℝ} (HZX : filter.eventually (λ n, X n ≤ Z n) F) (HZY : filter.eventually (λ n, Z n ≤ Y n) F) :
        (Z ⟶ x) F :=
  begin
    apply real.approaches_intro,
    intro ε Hε,
    apply filter.eventually_mp,
    rotate 1,
    apply filter.eventually_and,
    apply real.approaches_dest HX Hε,
    apply real.approaches_dest HY Hε,
    apply filter.eventually_mono,
    apply filter.eventually_and HZX HZY,
    intros x' Hlo Hdst,
    change abs (Z x' - x) < ε,
    cases em (x ≤ Z x') with HxleZ HxnleZ, -- annoying linear arith
    {have Y x' - x = (Z x' - x) + (Y x' - Z x'), by rewrite -sub_eq_sub_add_sub,
    have H : abs (Y x' - x) < ε, from and.right Hdst,
    rewrite this at H,
    have H'' : Y x' - Z x' ≥ 0, from sub_nonneg_of_le (and.right Hlo),
    have H' : Z x' - x ≥ 0, from sub_nonneg_of_le HxleZ,
    krewrite [abs_of_nonneg H', abs_of_nonneg (add_nonneg H' H'') at H],
    apply lt_of_add_lt_of_nonneg_left H H''},
    {have X x' - x = (Z x' - x) + (X x' - Z x'), by rewrite -sub_eq_sub_add_sub,
    have H : abs (X x' - x) < ε, from and.left Hdst,
    rewrite this at H,
    have H' : x - Z x' > 0, from sub_pos_of_lt (lt_of_not_ge HxnleZ),
    have H'2 : Z x' - x < 0,
      by rewrite [-neg_neg (Z x' - x)]; apply neg_neg_of_pos; rewrite [neg_sub]; apply H',
    have H'' : X x' - Z x' ≤ 0, from sub_nonpos_of_le (and.left Hlo),
    krewrite [abs_of_neg H'2, abs_of_neg (add_neg_of_neg_of_nonpos H'2 H'') at H, neg_add at H],
    apply lt_of_add_lt_of_nonneg_left H,
    apply neg_nonneg_of_nonpos H''}
  end

proposition approaches_of_abs_sub_approaches {F} (Habs : ((λ n, abs (X n - x)) ⟶ 0) F) :
            (X ⟶ x) F :=
  begin
    apply real.approaches_intro,
    intro ε Hε,
    apply set.filter.eventually_mono,
    apply real.approaches_dest Habs Hε,
    intro n Hn,
    have Hn' : abs (abs (X n - x) - 0) < ε, from Hn,
    rewrite [sub_zero at Hn', abs_abs at Hn'],
    exact Hn'
  end

proposition abs_sub_approaches_of_approaches {F} (HX : (X ⟶ x) F) :
            ((λ n, abs (X n - x)) ⟶ 0) F :=
  begin
    apply real.approaches_intro,
    intros ε Hε,
    apply set.filter.eventually_mono,
    apply real.approaches_dest HX Hε,
    intro n Hn,
    have Hn' : abs (abs (X n - x) - 0) < ε, by rewrite [sub_zero, abs_abs]; apply Hn,
    exact Hn'
  end

proposition bounded_of_approaches_real {F} (HX : (X ⟶ x) F) :
            ∃ K : ℝ, filter.eventually (λ n, abs (X n) ≤ K) F :=
  begin
    cases bounded_of_converges HX with K HK,
    existsi K + abs x,
    apply filter.eventually_mono HK,
    intro x' Hx',
    note Hle := abs_sub_abs_le_abs_sub (X x') x,
    apply le.trans,
    apply le_add_of_sub_right_le,
    apply Hle,
    apply add_le_add_right,
    apply Hx'
  end

proposition mul_approaches {F} (HX : (X ⟶ x) F) (HY : (Y ⟶ y) F) :
            ((λ n, X n * Y n) ⟶ x * y) F :=
    obtain K HK, from bounded_of_approaches_real HX,
    have Habsle : filter.eventually
         (λ n, abs (X n * Y n - x * y) ≤ K * abs (Y n - y) + abs y * abs (X n - x)) F, begin
      have Heq : ∀ n, X n * Y n - x * y = (X n * Y n - X n * y) + (X n * y - x * y),
        by intro n; rewrite [-sub_add_cancel (X n * Y n) (X n * y) at {1}, sub_eq_add_neg, *add.assoc],
      apply filter.eventually_mono HK,
      intro x' Hx',
      apply le.trans,
      rewrite Heq,
      apply abs_add_le_abs_add_abs,
      apply add_le_add,
      rewrite [-mul_sub_left_distrib, abs_mul],
      apply mul_le_mul_of_nonneg_right,
      apply Hx',
      apply abs_nonneg,
      rewrite [-mul_sub_right_distrib, abs_mul, mul.comm],
      apply le.refl
    end,
    have Hdifflim : ((λ n, abs (X n * Y n - x * y)) ⟶ 0) F, begin
      apply approaches_squeeze,
      rotate 2,
      intro,
      apply filter.eventually_mono HK,
      intro x' Hx',
      apply abs_nonneg,
      apply Habsle,
      apply approaches_constant,
      rewrite -{0}zero_add,
      apply add_approaches,
      krewrite -(mul_zero K),
      apply mul_left_approaches,
      apply abs_sub_approaches_of_approaches,
      exact HY,
      krewrite -(mul_zero (abs y)),
      apply mul_left_approaches,
      apply abs_sub_approaches_of_approaches,
      exact HX
    end,
    approaches_of_abs_sub_approaches Hdifflim

proposition mul_approaches_zero_of_approaches_zero_of_approaches (HX : (X ⟶ 0) F) (HY : (Y ⟶ y) F) :
            ((λ z, X z * Y z) ⟶ 0) F :=
  begin
    krewrite [-zero_mul y],
    apply mul_approaches,
    exact HX, exact HY
  end

proposition mul_approaches_zero_of_approaches_of_approaches_zero (HX : (X ⟶ y) F) (HY : (Y ⟶ 0) F) :
            ((λ z, X z * Y z) ⟶ 0) F :=
  begin
    have H : (λ z, X z * Y z) = (λ z, Y z * X z), from funext (λ a, !mul.comm),
    rewrite H,
    exact mul_approaches_zero_of_approaches_zero_of_approaches HY HX
  end

proposition abs_approaches_zero_of_approaches_zero (HX : (X ⟶ 0) F) : ((λ n, abs (X n)) ⟶ 0) F :=
norm_approaches_zero_of_approaches_zero HX

proposition approaches_zero_of_abs_approaches_zero (HX : ((λ n, abs (X n)) ⟶ 0) F) :
  (X ⟶ 0) F :=
approaches_zero_of_norm_approaches_zero HX

proposition abs_approaches_zero_iff :
  ((λ n, abs (X n)) ⟶ 0) F ↔ (X ⟶ 0) F :=
iff.intro approaches_zero_of_abs_approaches_zero abs_approaches_zero_of_approaches_zero
end limit_operations


/- monotone sequences -/

section monotone_sequences
open real set
variable {X : ℕ → ℝ}

proposition converges_to_seq_sup_of_nondecreasing (nondecX : nondecreasing X) {b : ℝ}
    (Hb : ∀ i, X i ≤ b) : X ⟶ sup (X ' univ) [at ∞] :=
real.approaches_at_infty_intro
(let sX := sup (X ' univ) in
have Xle : ∀ i, X i ≤ sX, from
  take i,
  have ∀ x, x ∈ X ' univ → x ≤ b, from
    (take x, assume H,
      obtain i [H' (Hi : X i = x)], from H,
      by rewrite -Hi; exact Hb i),
  show X i ≤ sX, from le_sup (mem_image_of_mem X !mem_univ) this,
have exX : ∃ x, x ∈ X ' univ,
  from exists.intro (X 0) (mem_image_of_mem X !mem_univ),
take ε, assume epos : ε > 0,
have sX - ε < sX, from !sub_lt_of_pos epos,
obtain x' [(H₁x' : x' ∈ X ' univ) (H₂x' : sX - ε < x')],
  from exists_mem_and_lt_of_lt_sup exX this,
obtain i [H' (Hi : X i = x')], from H₁x',
have Hi' : ∀ j, j ≥ i → sX - ε < X j, from
  take j, assume Hj, lt_of_lt_of_le (by rewrite Hi; apply H₂x') (nondecX Hj),
exists.intro i
  (take j, assume Hj : j ≥ i,
    have X j - sX ≤ 0, from sub_nonpos_of_le (Xle j),
    have eq₁ : abs (X j - sX) = sX - X j, by rewrite [abs_of_nonpos this, neg_sub],
    have sX - ε < X j, from lt_of_lt_of_le (by rewrite Hi; apply H₂x') (nondecX Hj),
    have sX < X j + ε, from lt_add_of_sub_lt_right this,
    have sX - X j < ε, from sub_lt_left_of_lt_add this,
    show (abs (X j - sX)) < ε, by rewrite eq₁; exact this))

proposition converges_to_seq_inf_of_nonincreasing (nonincX : nonincreasing X) {b : ℝ}
    (Hb : ∀ i, b ≤ X i) : X ⟶ inf (X ' univ) [at ∞] :=
have H₁ : ∃ x, x ∈ X ' univ, from exists.intro (X 0) (mem_image_of_mem X !mem_univ),
have H₂ : ∀ x, x ∈ X ' univ → b ≤ x, from
  (take x, assume H,
    obtain i [Hi₁ (Hi₂ : X i = x)], from H,
    show b ≤ x, by rewrite -Hi₂; apply Hb i),
have H₃ : {x : ℝ | -x ∈ X ' univ} = {x : ℝ | x ∈ (λ n, -X n) ' univ}, from calc
  {x : ℝ | -x ∈ X ' univ} = (λ y, -y) ' (X ' univ) : by rewrite image_neg_eq
                       ... = {x : ℝ | x ∈ (λ n, -X n) ' univ} : image_comp,
have H₄ : ∀ i, - X i ≤ - b, from take i, neg_le_neg (Hb i),
begin
  apply approaches_neg,
  -- need krewrite here
  krewrite [-sup_neg H₁ H₂, H₃, -nondecreasing_neg_iff at nonincX],
  apply converges_to_seq_sup_of_nondecreasing nonincX H₄
end

end monotone_sequences

/- x^n converges to 0 if abs x < 1 -/

section xn
open nat set

theorem pow_approaches_zero_at_infty {x : ℝ} (H : abs x < 1) :
  (λ n, x^n) ⟶ 0 [at ∞] :=
suffices H' : (λ n, (abs x)^n) ⟶ 0 [at ∞], from
  have (λ n, (abs x)^n) = (λ n, abs (x^n)), from funext (take n, eq.symm !abs_pow),
    by rewrite this at H'; exact approaches_zero_of_abs_approaches_zero H',
let  aX := (λ n, (abs x)^n),
    iaX := real.inf (aX ' univ),
    asX := (λ n, (abs x)^(succ n)) in
have noninc_aX : nonincreasing aX, from
  nonincreasing_of_forall_ge_succ
    (take i,
      have (abs x) * (abs x)^i ≤ 1 * (abs x)^i,
        from mul_le_mul_of_nonneg_right (le_of_lt H) (!pow_nonneg_of_nonneg !abs_nonneg),
      have (abs x) * (abs x)^i ≤ (abs x)^i, by krewrite one_mul at this; exact this,
      show (abs x) ^ (succ i) ≤ (abs x)^i, by rewrite pow_succ; apply this),
have bdd_aX : ∀ i, 0 ≤ aX i, from take i, !pow_nonneg_of_nonneg !abs_nonneg,
have aXconv : aX ⟶ iaX [at ∞], proof converges_to_seq_inf_of_nonincreasing noninc_aX bdd_aX qed,
have asXconv : asX ⟶ iaX [at ∞], from tendsto_succ_at_infty aXconv,
have asXconv' : asX ⟶ (abs x) * iaX [at ∞], from mul_left_approaches (abs x) aXconv,
have iaX = (abs x) * iaX, from sorry, -- converges_to_seq_unique asXconv asXconv',
have iaX = 0, from eq_zero_of_mul_eq_self_left (ne_of_lt H) (eq.symm this),
show aX ⟶ 0 [at ∞], begin rewrite -this, exact aXconv end --from this ▸ aXconv

end xn

/- continuity on the reals -/

/-namespace real
open topology set
open normed_vector_space

section
variable {f : ℝ → ℝ}

theorem continuous_dest (H : continuous f) :
  ∀ x : ℝ, ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ,
    abs (x' - x) < δ → abs (f x' - f x) < ε :=
normed_vector_space.continuous_dest H

theorem continuous_intro
  (H : ∀ x : ℝ, ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ,
    abs (x' - x) < δ → abs (f x' - f x) < ε) :
  continuous f :=
normed_vector_space.continuous_intro H

theorem continuous_at_dest {x : ℝ} (H : continuous_at f x) :
         ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ, abs (x' - x) < δ → abs (f x' - f x) < ε) :=
normed_vector_space.continuous_at_dest H

theorem continuous_at_intro {x : ℝ}
  (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ,
    abs (x' - x) < δ → abs (f x' - f x) < ε) :
  continuous_at f x :=
normed_vector_space.continuous_at_intro H

theorem continuous_at_within_intro {x : ℝ} {s : set ℝ}
        (H : ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → abs (x' - x) < δ → abs ((f x') - (f x)) < ε) :
  continuous_at_on f x s :=
normed_vector_space.continuous_at_within_intro H


theorem continuous_at_on_dest {x : ℝ} {s : set ℝ} (Hfx : continuous_at_on f x s) :
         ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → abs (x' - x) < δ → abs ((f x') - (f x)) < ε :=
normed_vector_space.continuous_at_on_dest Hfx

theorem continuous_on_intro {s : set ℝ}
        (H : ∀ x ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → abs (x' - x) < δ → abs ((f x') - (f x)) < ε) :
        continuous_on f s :=
normed_vector_space.continuous_on_intro H

theorem continuous_on_dest {s : set ℝ} (H : continuous_on f s) {x : ℝ} (Hxs : x ∈ s) :
        ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → abs (x' - x) < δ → abs ((f x') - (f x)) < ε :=
normed_vector_space.continuous_on_dest H Hxs

end

section
variable {f : ℕ → ℝ}
proposition approaches_at_infty_intro {y : ℝ}
    (H : ∀ ε, ε > 0 → ∃ N, ∀ n, n ≥ N → abs ((f n) - y) < ε) :
  f ⟶ y [at ∞] :=
normed_vector_space.approaches_at_infty_intro H

proposition approaches_at_infty_dest {y : ℝ}
    (H : f ⟶ y [at ∞]) ⦃ε : ℝ⦄ (εpos : ε > 0) :
  ∃ N, ∀ ⦃n⦄, n ≥ N → abs ((f n) - y) < ε :=
approaches_at_infty_dest H εpos

proposition approaches_at_infty_iff (y : ℝ) :
  f ⟶ y [at ∞] ↔ (∀ ε, ε > 0 → ∃ N, ∀ ⦃n⦄, n ≥ N → abs((f n) - y) < ε) :=
iff.intro approaches_at_infty_dest approaches_at_infty_intro

end

section
variable {f : ℝ → ℝ}
proposition approaches_at_dest  {y x : ℝ}
    (H : f ⟶ y [at x]) ⦃ε : ℝ⦄ (εpos : ε > 0) :
  ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, abs (x' - x) < δ → x' ≠ x → abs ((f x') - y) < ε :=
approaches_at_dest H εpos

proposition approaches_at_intro {y x : ℝ}
    (H : ∀ ε, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, abs (x' - x) < δ → x' ≠ x → abs ((f x') - y) < ε) :
  f ⟶ y [at x] :=
approaches_at_intro H

proposition approaches_at_iff (y x : ℝ) : f ⟶ y [at x] ↔
    (∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, abs (x' - x) < δ → x' ≠ x → abs ((f x') - y) < ε) :=
iff.intro approaches_at_dest approaches_at_intro

/-proposition approaches_seq_real_intro {X : ℕ → ℝ} {y : ℝ}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) < ε) :
  (X ⟶ y [at ∞]) := metric_space.approaches_at_infty_intro H

proposition approaches_seq_real_elim {X : ℕ → ℝ} {y : ℝ} (H : X ⟶ y [at ∞]) :
    ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) < ε := metric_space.approaches_at_infty_dest H

proposition approaches_seq_real_intro' {X : ℕ → ℝ} {y : ℝ}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) ≤ ε) :
  (X ⟶ y [at ∞]) :=
approaches_at_infty_intro' H-/

end

end real-/

section continuous
open topology
variable {f : ℝ → ℝ}
variable (Hf : continuous f)
include Hf

theorem pos_on_nbhd_of_cts_of_pos {b : ℝ} (Hb : f b > 0) :
                ∃ δ : ℝ, δ > 0 ∧ ∀ y, abs (y - b) < δ → f y > 0 :=
  begin
    let Hcont := real.continuous_dest Hf b Hb,
    cases Hcont with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro y Hy,
    let Hy' := and.right Hδ y Hy,
    note Hlt := sub_lt_of_abs_sub_lt_left Hy',
    rewrite sub_self at Hlt,
    assumption
  end

theorem neg_on_nbhd_of_cts_of_neg {b : ℝ} (Hb : f b < 0) :
                ∃ δ : ℝ, δ > 0 ∧ ∀ y, abs (y - b) < δ → f y < 0 :=
  begin
    let Hcont := real.continuous_dest Hf b (neg_pos_of_neg Hb),
    cases Hcont with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro y Hy,
    let Hy' := and.right Hδ y Hy,
    let Hlt := sub_lt_of_abs_sub_lt_right Hy',
    note Hlt' := lt_add_of_sub_lt_left Hlt,
    rewrite [add.comm at Hlt', -sub_eq_add_neg at Hlt', sub_self at Hlt'],
    assumption
  end

theorem continuous_mul_of_continuous {g : ℝ → ℝ} (Hcong : continuous g) :
        continuous (λ x, f x * g x) :=
  begin
    apply continuous_of_forall_continuous_at,
    intro x,
    apply continuous_at_of_tendsto_at,
    apply mul_approaches,
    all_goals apply tendsto_at_of_continuous_at,
    all_goals apply forall_continuous_at_of_continuous,
    apply Hf,
    apply Hcong
  end

end continuous
