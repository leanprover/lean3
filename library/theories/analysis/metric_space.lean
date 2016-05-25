/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Metric spaces.

Authors: Jeremy Avigad, Robert Y. Lewis
-/
import data.real.complete data.pnat ..topology.continuous ..topology.limit data.set
open nat real eq.ops classical set prod set.filter topology interval

structure metric_space [class] (M : Type) : Type :=
  (dist : M → M → ℝ)
  (dist_self : ∀ x : M, dist x x = 0)
  (eq_of_dist_eq_zero : ∀ {x y : M}, dist x y = 0 → x = y)
  (dist_comm : ∀ x y : M, dist x y = dist y x)
  (dist_triangle : ∀ x y z : M, dist x z ≤ dist x y + dist y z)

namespace analysis

section metric_space_M
variables {M : Type} [metric_space M]

definition dist (x y : M) : ℝ := metric_space.dist x y

proposition dist_self (x : M) : dist x x = 0 := metric_space.dist_self x

proposition eq_of_dist_eq_zero {x y : M} (H : dist x y = 0) : x = y :=
metric_space.eq_of_dist_eq_zero H

proposition dist_comm (x y : M) : dist x y = dist y x := metric_space.dist_comm x y

proposition dist_eq_zero_iff (x y : M) : dist x y = 0 ↔ x = y :=
iff.intro eq_of_dist_eq_zero (suppose x = y, this ▸ !dist_self)

proposition dist_triangle (x y z : M) : dist x z ≤ dist x y + dist y z :=
metric_space.dist_triangle x y z

proposition dist_nonneg (x y : M) : 0 ≤ dist x y :=
have dist x y + dist y x ≥ 0, by rewrite -(dist_self x); apply dist_triangle,
have 2 * dist x y ≥ 0,
  by krewrite [-real.one_add_one, right_distrib, +one_mul, dist_comm at {2}]; apply this,
nonneg_of_mul_nonneg_left this two_pos

proposition dist_pos_of_ne {x y : M} (H : x ≠ y) : dist x y > 0 :=
lt_of_le_of_ne !dist_nonneg (suppose 0 = dist x y, H (iff.mp !dist_eq_zero_iff this⁻¹))

proposition ne_of_dist_pos {x y : M} (H : dist x y > 0) : x ≠ y :=
suppose x = y,
have H1 : dist x x > 0, by rewrite this at {2}; exact H,
by rewrite dist_self at H1; apply not_lt_self _ H1

proposition eq_of_forall_dist_le {x y : M} (H : ∀ ε, ε > 0 → dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_zero_of_nonneg_of_forall_le !dist_nonneg H)


/- instantiate metric space as a topology -/

definition open_ball (x : M) (ε : ℝ) := {y | dist y x < ε}

theorem open_ball_eq_empty_of_nonpos (x : M) {ε : ℝ} (Hε : ε ≤ 0) : open_ball x ε = ∅ :=
  begin
    apply eq_empty_of_forall_not_mem,
    intro y Hlt,
    apply not_lt_of_ge (dist_nonneg y x),
    apply lt_of_lt_of_le Hlt Hε
  end

theorem pos_of_mem_open_ball {x : M} {ε : ℝ} {u : M} (Hu : u ∈ open_ball x ε) : ε > 0 :=
  begin
    apply lt_of_not_ge,
    intro Hge,
    note Hop := open_ball_eq_empty_of_nonpos x Hge,
    rewrite Hop at Hu,
    apply not_mem_empty _ Hu
  end

theorem mem_open_ball (x : M) {ε : ℝ} (H : ε > 0) : x ∈ open_ball x ε :=
  show dist x x < ε, by rewrite dist_self; assumption

definition closed_ball (x : M) (ε : ℝ) := {y | dist y x ≤ ε}

theorem closed_ball_eq_compl (x : M) (ε : ℝ) : closed_ball x ε = - {y | dist y x > ε} :=
ext (take y, iff.intro
  (suppose dist y x ≤ ε, not_lt_of_ge this)
  (suppose ¬ dist y x > ε, le_of_not_gt this))

variable (M)

definition open_sets_basis : set (set M) := { s | ∃ x, ∃ ε, s = open_ball x ε }

definition metric_topology [instance] : topology M := topology.generated_by (open_sets_basis M)

variable {M}

theorem open_ball_mem_open_sets_basis (x : M) (ε : ℝ) : open_ball x ε ∈ open_sets_basis M :=
  exists.intro x (exists.intro ε rfl)

theorem Open_open_ball (x : M) (ε : ℝ) : Open (open_ball x ε) :=
  by apply generators_mem_topology_generated_by; apply open_ball_mem_open_sets_basis

theorem closed_closed_ball (x : M) {ε : ℝ} (H : ε > 0) : closed (closed_ball x ε) :=
Open_of_forall_exists_Open_nbhd
  (take y, suppose ¬ dist y x ≤ ε,
    have dist y x > ε, from lt_of_not_ge this,
    let B := open_ball y (dist y x - ε) in
    have y ∈ B, from mem_open_ball y (sub_pos_of_lt this),
    have B ⊆ - closed_ball x ε, from
      take y',
      assume Hy'y : dist y' y < dist y x - ε,
      assume Hy'x : dist y' x ≤ ε,
      show false, from not_lt_self (dist y x)
        (calc
          dist y x ≤ dist y y' + dist y' x   : dist_triangle
            ... < dist y x - ε + dist y' x   : by rewrite dist_comm; apply add_lt_add_right Hy'y
            ... ≤ dist y x - ε + ε           : add_le_add_left Hy'x
            ... = dist y x                   : by rewrite [sub_add_cancel]),
    exists.intro B (and.intro (Open_open_ball _ _) (and.intro `y ∈ B` this)))

proposition open_ball_subset_open_ball_of_le (x : M) {r₁ r₂ : ℝ} (H : r₁ ≤ r₂) :
  open_ball x r₁ ⊆ open_ball x r₂ :=
take y, assume ymem, lt_of_lt_of_le ymem H

theorem exists_open_ball_subset_of_Open_of_mem {U : set M} (HU : Open U) {x : M} (Hx : x ∈ U) :
        ∃ (r : ℝ), r > 0 ∧ open_ball x r ⊆ U :=
begin
  induction HU with s sbasis s t sbasis tbasis ihs iht S Sbasis ihS,
    {cases sbasis with x' aux, cases aux with ε seq,
      have x ∈ open_ball x' ε, by rewrite -seq; exact Hx,
      have εpos : ε > 0, from pos_of_mem_open_ball this,
      have ε - dist x x' > 0, from sub_pos_of_lt `x ∈ open_ball x' ε`,
      existsi (ε - dist x x'), split, exact this, rewrite seq,
      show open_ball x (ε - dist x x') ⊆ open_ball x' ε, from
        take y, suppose dist y x < ε - dist x x',
        calc
          dist y x' ≤ dist y x + dist x x'      : dist_triangle
                ... < ε - dist x x' + dist x x' : add_lt_add_right this
                ... = ε                         : sub_add_cancel},
    {existsi 1, split, exact zero_lt_one, exact subset_univ _},
    {cases ihs (and.left Hx) with rs aux, cases aux with rspos ballrs_sub,
      cases iht (and.right Hx) with rt aux, cases aux with rtpos ballrt_sub,
      let rmin := min rs rt,
      existsi rmin, split, exact lt_min rspos rtpos,
      have open_ball x rmin ⊆ s,
        from subset.trans (open_ball_subset_open_ball_of_le x !min_le_left) ballrs_sub,
      have open_ball x rmin ⊆ t,
        from subset.trans (open_ball_subset_open_ball_of_le x !min_le_right) ballrt_sub,
      show open_ball x (min rs rt) ⊆ s ∩ t,
        by apply subset_inter; repeat assumption},
  cases Hx with s aux, cases aux with sS xs,
  cases (ihS sS xs) with r aux, cases aux with rpos ballr_sub,
  existsi r, split, exact rpos,
  show open_ball x r ⊆ ⋃₀ S, from subset.trans ballr_sub (subset_sUnion_of_mem sS)
end

/- limits in metric spaces -/

proposition eventually_nhds_intro {P : M → Prop} {ε : ℝ} (εpos : ε > 0) {x : M}
    (H : ∀ x', dist x' x < ε → P x') :
  eventually P (nhds x) :=
topology.eventually_nhds_intro (Open_open_ball x ε) (mem_open_ball x εpos) H

proposition eventually_nhds_dest {P : M → Prop} {x : M} (H : eventually P (nhds x)) :
  ∃ ε, ε > 0 ∧ ∀ x', dist x' x < ε → P x' :=
obtain s [(Os : Open s) [(xs : x ∈ s) (Hs : ∀₀ x' ∈ s, P x')]],
  from topology.eventually_nhds_dest H,
obtain ε [(εpos : ε > 0) (Hε : open_ball x ε ⊆ s)],
  from exists_open_ball_subset_of_Open_of_mem Os xs,
exists.intro ε (and.intro εpos
  (take x', suppose dist x' x < ε,
    have x' ∈ s, from Hε this,
    show P x', from Hs this))

proposition eventually_nhds_iff (P : M → Prop) (x : M) :
  eventually P (nhds x) ↔ (∃ ε, ε > 0 ∧ ∀ x', dist x' x < ε → P x') :=
iff.intro eventually_nhds_dest
  (assume H, obtain ε [εpos Hε], from H, eventually_nhds_intro εpos Hε)

proposition eventually_dist_lt_nhds (x : M) {ε : ℝ} (εpos : ε > 0) :
   eventually (λ x', dist x' x < ε) (nhds x) :=
eventually_nhds_intro εpos (λ x' H, H)

proposition eventually_at_within_intro {P : M → Prop} {ε : ℝ} (εpos : ε > 0) {x : M} {s : set M}
  (H : ∀₀ x' ∈ s, dist x' x < ε → x' ≠ x → P x') :
 eventually P [at x within s] :=
topology.eventually_at_within_intro (Open_open_ball x ε) (mem_open_ball x εpos)
  (λ x' x'mem x'ne x's, H x's x'mem x'ne)

proposition eventually_at_within_dest {P : M → Prop} {x : M} {s : set M}
    (H : eventually P [at x within s]) :
  ∃ ε, ε > 0 ∧ ∀₀ x' ∈ s, dist x' x < ε → x' ≠ x → P x' :=
obtain t [(Ot : Open t) [(xt : x ∈ t) (Ht : ∀₀ x' ∈ t, x' ≠ x → x' ∈ s → P x')]],
  from topology.eventually_at_within_dest H,
obtain ε [(εpos : ε > 0) (Hε : open_ball x ε ⊆ t)],
  from exists_open_ball_subset_of_Open_of_mem Ot xt,
exists.intro ε (and.intro εpos
  (take x', assume x's distx'x x'nex,
    have x' ∈ t, from Hε distx'x,
    show P x', from Ht this x'nex x's))

proposition eventually_at_within_iff (P : M → Prop) (x : M) (s : set M) :
  eventually P [at x within s] ↔  ∃ ε, ε > 0 ∧ ∀₀ x' ∈ s, dist x' x < ε → x' ≠ x → P x' :=
iff.intro eventually_at_within_dest
  (λ H, obtain ε [εpos Hε], from H, eventually_at_within_intro εpos Hε)

proposition eventually_at_intro {P : M → Prop} {ε : ℝ} (εpos : ε > 0) {x : M}
    (H : ∀ x', dist x' x < ε → x' ≠ x → P x') :
 eventually P [at x] :=
topology.eventually_at_intro (Open_open_ball x ε) (mem_open_ball x εpos)
  (λ x' x'mem x'ne, H x' x'mem x'ne)

proposition eventually_at_dest {P : M → Prop} {x : M} (H : eventually P [at x]) :
  ∃ ε, ε > 0 ∧ ∀ ⦃x'⦄, dist x' x < ε → x' ≠ x → P x' :=
obtain ε [εpos Hε], from eventually_at_within_dest H,
exists.intro ε (and.intro εpos (λ x', Hε x' (mem_univ x')))

proposition eventually_at_iff (P : M → Prop) (x : M) :
  eventually P [at x] ↔  ∃ ε, ε > 0 ∧ ∀ ⦃x'⦄, dist x' x < ε → x' ≠ x → P x' :=
iff.intro eventually_at_dest (λ H, obtain ε [εpos Hε], from H, eventually_at_intro εpos Hε)

end metric_space_M

namespace metric_space
variables {M : Type} [metric_space M]

section approaches
  variables {X : Type} {F : filter X} {f : X → M} {y : M}

  proposition approaches_intro (H : ∀ ε, ε > 0 → eventually (λ x, dist (f x) y < ε) F) :
    (f ⟶ y) F :=
  tendsto_intro
    (take P, assume eventuallyP,
      obtain ε [(εpos : ε > 0) (Hε : ∀ x', dist x' y < ε → P x')],
        from eventually_nhds_dest eventuallyP,
      show eventually (λ x, P (f x)) F,
        from eventually_mono (H ε εpos) (λ x Hx, Hε (f x) Hx))

  proposition approaches_dest (H : (f ⟶ y) F) {ε : ℝ} (εpos : ε > 0) :
    eventually (λ x, dist (f x) y < ε) F :=
  tendsto_dest H (eventually_dist_lt_nhds y εpos)

  variables (F f y)

  proposition approaches_iff : (f ⟶ y) F ↔ (∀ ε, ε > 0 → eventually (λ x, dist (f x) y < ε) F) :=
  iff.intro approaches_dest approaches_intro

end approaches

-- here we full unwrap two particular kinds of convergence3
-- TODO: put these in metric space namespace? (will have similar in normed_space


proposition approaches_at_infty_intro {f : ℕ → M} {y : M}
    (H : ∀ ε, ε > 0 → ∃ N, ∀ n, n ≥ N → dist (f n) y < ε) :
  f ⟶ y [at ∞] :=
approaches_intro (λ ε εpos, obtain N HN, from H ε εpos,
  eventually_at_infty_intro HN)

proposition approaches_at_infty_dest {f : ℕ → M} {y : M}
    (H : f ⟶ y [at ∞]) ⦃ε : ℝ⦄ (εpos : ε > 0) :
  ∃ N, ∀ ⦃n⦄, n ≥ N → dist (f n) y < ε :=
have eventually (λ x, dist (f x) y < ε) [at ∞], from approaches_dest H εpos,
eventually_at_infty_dest this

proposition approaches_at_infty_iff (f : ℕ → M) (y : M) :
  f ⟶ y [at ∞] ↔ (∀ ε, ε > 0 → ∃ N, ∀ ⦃n⦄, n ≥ N → dist (f n) y < ε) :=
iff.intro approaches_at_infty_dest approaches_at_infty_intro

section metric_space_N
variables {N : Type} [metric_space N]

proposition approaches_at_dest {f : M → N} {y : N} {x : M}
    (H : f ⟶ y [at x]) ⦃ε : ℝ⦄ (εpos : ε > 0) :
  ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → x' ≠ x → dist (f x') y < ε :=
have eventually (λ x, dist (f x) y < ε) [at x],
  from approaches_dest H εpos,
eventually_at_dest this

proposition approaches_at_intro {f : M → N} {y : N} {x : M}
    (H : ∀ ε, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → x' ≠ x → dist (f x') y < ε) :
  f ⟶ y [at x] :=
approaches_intro (λ ε εpos,
  obtain δ [δpos Hδ], from H ε εpos,
  eventually_at_intro δpos Hδ)

proposition approaches_at_iff (f : M → N) (y : N) (x : M) : f ⟶ y [at x] ↔
    (∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → x' ≠ x → dist (f x') y < ε) :=
iff.intro approaches_at_dest approaches_at_intro

end metric_space_N
end metric_space -- close namespace

section metric_space_M
variables {M : Type} [metric_space M]
-- TODO: remove this. It is only here temporarily, because it is used in normed_space (JA)
-- It is used in the definition of a complete metric space below, but I think it doesn't
-- have to be a class (RL)
abbreviation converges_seq [class] (X : ℕ → M) : Prop := ∃ y, X ⟶ y [at ∞]

-- TODO: refactor
-- the same, with ≤ in place of <; easier to prove, harder to use
definition approaches_at_infty_intro' {X : ℕ → M} {y : M}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → dist (X n) y ≤ ε) :
  (X ⟶ y) [at ∞] :=
metric_space.approaches_at_infty_intro
take ε, assume epos : ε > 0,
  have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
  obtain N HN, from H e2pos,
  exists.intro N
    (take n, suppose n ≥ N,
      calc
        dist (X n) y ≤ ε / 2 : HN _ `n ≥ N`
                 ... < ε     : div_two_lt_of_pos epos)

-- TODO: prove more generally
proposition approaches_at_infty_unique {X : ℕ → M} {y₁ y₂ : M}
  (H₁ : X ⟶ y₁ [at ∞]) (H₂ : X ⟶ y₂ [at ∞]) : y₁ = y₂ :=
eq_of_forall_dist_le
  (take ε, suppose ε > 0,
    have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
    obtain N₁ (HN₁ : ∀ {n}, n ≥ N₁ → dist (X n) y₁ < ε / 2),
      from metric_space.approaches_at_infty_dest H₁ e2pos,
    obtain N₂ (HN₂ : ∀ {n}, n ≥ N₂ → dist (X n) y₂ < ε / 2),
      from metric_space.approaches_at_infty_dest H₂ e2pos,
    let N := max N₁ N₂ in
    have dN₁ : dist (X N) y₁ < ε / 2, from HN₁ !le_max_left,
    have dN₂ : dist (X N) y₂ < ε / 2, from HN₂ !le_max_right,
    have dist y₁ y₂ < ε, from calc
      dist y₁ y₂ ≤ dist y₁ (X N) + dist (X N) y₂ : dist_triangle
             ... = dist (X N) y₁ + dist (X N) y₂ : dist_comm
             ... < ε / 2 + ε / 2                 : add_lt_add dN₁ dN₂
             ... = ε                             : add_halves,
    show dist y₁ y₂ ≤ ε, from le_of_lt this)

/- TODO: revise

definition converges_seq [class] (X : ℕ → M) : Prop := ∃ y, X ⟶ y in ℕ

noncomputable definition limit_seq (X : ℕ → M) [H : converges_seq X] : M := some H

proposition converges_to_limit_seq (X : ℕ → M) [H : converges_seq X] :
  (X ⟶ limit_seq X in ℕ) :=
some_spec H

proposition eq_limit_of_converges_to_seq {X : ℕ → M} {y : M} (H : X ⟶ y in ℕ) :
  y = @limit_seq M _ X (exists.intro y H) :=
converges_to_seq_unique H (@converges_to_limit_seq M _ X (exists.intro y H))

proposition converges_to_seq_offset_left {X : ℕ → M} {y : M} (k : ℕ) (H : X ⟶ y in ℕ) :
  (λ n, X (k + n)) ⟶ y in ℕ :=
have aux : (λ n, X (k + n)) = (λ n, X (n + k)), from funext (take n, by rewrite add.comm),
by rewrite aux; exact converges_to_seq_offset k H

proposition converges_to_seq_of_converges_to_seq_offset_left
    {X : ℕ → M} {y : M} {k : ℕ} (H : (λ n, X (k + n)) ⟶ y in ℕ) :
  X ⟶ y in ℕ :=
have aux : (λ n, X (k + n)) = (λ n, X (n + k)), from funext (take n, by rewrite add.comm),
by rewrite aux at H; exact converges_to_seq_of_converges_to_seq_offset H
-/

proposition bounded_of_converges_seq {X : ℕ → M} {x : M} (H : X ⟶ x [at ∞]) :
            ∃ K : ℝ, ∀ n : ℕ, dist (X n) x ≤ K :=
  have eventually (λ n, dist (X n) x < 1) [at ∞],
    from metric_space.approaches_dest H zero_lt_one,
  obtain N (HN : ∀ n, n ≥ N → dist (X n) x < 1),
    from eventually_at_infty_dest this,
  let K := max 1 (Max i ∈ '(-∞, N), dist (X i) x) in
  exists.intro K
    (take n,
      if Hn : n < N then
        show dist (X n) x ≤ K,
          from le.trans (le_Max _ Hn) !le_max_right
      else
        show dist (X n) x ≤ K,
          from le.trans (le_of_lt (HN n (le_of_not_gt Hn))) !le_max_left)

proposition bounded_of_converges {A : Type} {X : A → M} {x : M} {F} (H : (X ⟶ x) F) :
            ∃ K : ℝ, eventually (λ n, dist (X n) x ≤ K) F :=
  begin
    note H' := metric_space.approaches_dest H zero_lt_one,
    existsi 1,
    apply eventually_mono H',
    intro x' Hx',
    apply le_of_lt Hx'
  end

/-proposition converges_to_seq_of_converges_to_seq_offset_succ
    {X : ℕ → M} {y : M} (H : (λ n, X (succ n)) ⟶ y [at ∞]) :
  X ⟶ y [at ∞] :=
@converges_to_seq_of_converges_to_seq_offset M _ X y 1 H-/
/-
proposition converges_to_seq_offset_iff (X : ℕ → M) (y : M) (k : ℕ) :
  ((λ n, X (n + k)) ⟶ y in ℕ) ↔ (X ⟶ y in ℕ) :=
iff.intro converges_to_seq_of_converges_to_seq_offset !converges_to_seq_offset

proposition converges_to_seq_offset_left_iff (X : ℕ → M) (y : M) (k : ℕ) :
  ((λ n, X (k + n)) ⟶ y in ℕ) ↔ (X ⟶ y in ℕ) :=
iff.intro converges_to_seq_of_converges_to_seq_offset_left !converges_to_seq_offset_left

proposition converges_to_seq_offset_succ_iff (X : ℕ → M) (y : M) :
  ((λ n, X (succ n)) ⟶ y in ℕ) ↔ (X ⟶ y in ℕ) :=
iff.intro converges_to_seq_of_converges_to_seq_offset_succ !converges_to_seq_offset_succ
-/

/- cauchy sequences -/

definition cauchy (X : ℕ → M) : Prop :=
∀ ε : ℝ, ε > 0 → ∃ N, ∀ m n, m ≥ N → n ≥ N → dist (X m) (X n) < ε

proposition cauchy_of_converges_seq {X : ℕ → M} (H : ∃ y, X ⟶ y [at ∞]) : cauchy X :=
take ε, suppose ε > 0,
  obtain y (Hy : X ⟶ y [at ∞]), from H,
  have e2pos : ε / 2 > 0, from div_pos_of_pos_of_pos `ε > 0` two_pos,
  have eventually (λ n, dist (X n) y < ε / 2) [at ∞], from metric_space.approaches_dest Hy e2pos,
  obtain N (HN : ∀ {n}, n ≥ N → dist (X n) y < ε / 2), from eventually_at_infty_dest this,
    exists.intro N
      (take m n, suppose m ≥ N, suppose n ≥ N,
        have dN₁ : dist (X m) y < ε / 2, from HN `m ≥ N`,
        have dN₂ : dist (X n) y < ε / 2, from HN `n ≥ N`,
        show dist (X m) (X n) < ε, from calc
          dist (X m) (X n) ≤ dist (X m) y + dist y (X n) : dist_triangle
                       ... = dist (X m) y + dist (X n) y : dist_comm
                       ... < ε / 2 + ε / 2               : add_lt_add dN₁ dN₂
                       ... = ε                           : add_halves)

end metric_space_M

/- convergence of a function at a point -/

section metric_space_M_N
variables {M N : Type} [metric_space M] [metric_space N]


-- TODO: refactor
section
open pnat rat

theorem cnv_real_of_cnv_nat {X : ℕ → M} {c : M} (H : ∀ n : ℕ, dist (X n) c < 1 / (real.of_nat n + 1)) :
        ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → dist (X n) c < ε :=
  begin
    intros ε Hε,
    cases ex_rat_pos_lower_bound_of_pos Hε with q Hq,
    cases Hq with Hq1 Hq2,
    cases pnat_bound Hq1 with p Hp,
    existsi pnat.nat_of_pnat p,
    intros n Hn,
    apply lt_of_lt_of_le,
    apply H,
    apply le.trans,
    rotate 1,
    apply Hq2,
    have Hrat : of_rat (inv p) ≤ of_rat q, from of_rat_le_of_rat_of_le Hp,
    apply le.trans,
    rotate 1,
    exact Hrat,
    change 1 / (of_nat n + 1) ≤ of_rat ((1 : ℚ) / (rat_of_pnat p)),
    rewrite [of_rat_divide, of_rat_one],
    eapply one_div_le_one_div_of_le,
    krewrite -of_rat_zero,
    apply of_rat_lt_of_rat_of_lt,
    apply rat_of_pnat_is_pos,
    change of_nat (nat_of_pnat p) ≤ n + 1,
    krewrite [-real.of_nat_add],
    apply real.of_nat_le_of_nat_of_le,
    apply le_add_of_le_right,
    assumption
  end
end

-- TODO : refactor
theorem converges_to_at_of_all_conv_seqs {f : M → N} (c : M) (l : N)
  (Hseq : ∀ X : ℕ → M, (eventually (λ n, X n ≠ c) [at ∞] ∧ (X ⟶ c [at ∞])) → ((λ n : ℕ, f (X n)) ⟶ l [at ∞]))
  : f ⟶ l [at c] :=
  begin
    eapply by_contradiction,
    intro Hnot,
    cases exists_not_of_not_forall (λ H, Hnot (metric_space.approaches_at_intro H)) with ε Hε,
    cases and_not_of_not_implies Hε with H1 H2,
    note H3' := forall_not_of_not_exists H2,
    have H3 : ∀ δ, δ > 0 → (∃ x', dist x' c < δ ∧ x' ≠ c ∧ dist (f x') l ≥ ε), begin
      intro δ Hδ,
      cases exists_not_of_not_forall (or.resolve_left (not_or_not_of_not_and' (H3' δ)) (not_not_intro Hδ))
        with x' Hx',
      existsi x',
      rewrite [2 not_implies_iff_and_not at Hx', ge_iff_not_lt],
      exact Hx'
    end,
    let S := λ (n : ℕ) (x : M), 0 < dist x c ∧ dist x c < 1 / (of_nat n + 1) ∧ dist (f x) l ≥ ε,
    have HS : ∀ n : ℕ, ∃ m : M, S n m, begin
      intro k,
      have Hpos : 0 < of_nat k + 1, from of_nat_succ_pos k,
      cases H3 (1 / (k + 1)) (one_div_pos_of_pos Hpos) with x' Hx',
      cases Hx' with Hne Hx',
      cases Hx' with Hdistl Hdistg,
      existsi x',
      esimp,
      split,
      apply dist_pos_of_ne,
      assumption,
      split,
      repeat assumption
    end,
    let X := λ n, some (HS n),
    have H4 : (eventually (λ n, X n ≠ c) [at ∞]) ∧ (X ⟶ c [at ∞]), begin
      split,
      {fapply @eventually_at_infty_intro,
      exact 0,
      intro n Hn,
      note Hspec := some_spec (HS n),
      esimp, esimp at Hspec,
      cases Hspec,
      apply ne_of_dist_pos,
      assumption},
      {intro,
      apply metric_space.approaches_at_infty_intro,
      apply cnv_real_of_cnv_nat,
      intro m,
      note Hspec := some_spec (HS m),
      esimp, esimp at Hspec,
      cases Hspec with Hspec1 Hspec2,
      cases Hspec2,
      assumption}
    end,
    have H5 : (λ n, f (X n)) ⟶ l [at ∞], from Hseq X H4,
    note H6 := metric_space.approaches_at_infty_dest H5 H1,
    cases H6 with Q HQ,
    note HQ' := HQ !le.refl,
    esimp at HQ',
    apply absurd HQ',
    apply not_lt_of_ge,
    note H7 := some_spec (HS Q),
    esimp at H7,
    cases H7 with H71 H72,
    cases H72,
    assumption
  end

end metric_space_M_N

namespace metric_space

section continuity
variables {M N : Type} [Hm : metric_space M] [Hn : metric_space N]
include Hm Hn
open topology set

-- the ε - δ definition of continuity is equivalent to the topological definition

theorem continuous_at_within_intro {f : M → N} {x : M} {s : set M}
        (H : ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → dist x' x < δ → dist (f x') (f x) < ε) :
  continuous_at_on f x s :=
  begin
    intro U Uopen HfU,
    cases exists_open_ball_subset_of_Open_of_mem Uopen HfU with r Hr,
    cases Hr with Hr HUr,
    cases H Hr with δ Hδ,
    cases Hδ with Hδ Hx'δ,
    existsi open_ball x δ,
    split,
    apply Open_open_ball,
    split,
    apply mem_open_ball,
    exact Hδ,
    intro y Hy,
    apply mem_preimage,
    apply HUr,
    apply Hx'δ,
    apply and.right Hy,
    apply and.left Hy
  end

theorem continuous_at_on_dest {f : M → N} {x : M} {s : set M} (Hfx : continuous_at_on f x s) :
         ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → dist x' x < δ → dist (f x') (f x) < ε :=
  begin
    intros ε Hε,
    cases @Hfx (open_ball (f x) ε) !Open_open_ball (mem_open_ball _ Hε) with V HV,
    cases HV with HV HVx,
    cases HVx with HVx HVf,
    cases exists_open_ball_subset_of_Open_of_mem HV HVx with δ Hδ,
    cases Hδ with Hδ Hδx,
    existsi δ,
    split,
    exact Hδ,
    intro x' Hx's Hx',
    apply HVf,
    apply and.intro,
    apply Hδx,
    exact Hx',
    exact Hx's
  end

theorem continuous_at_intro {f : M → N} {x : M}
        (H : ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → dist (f x') (f x) < ε) :
        continuous_at f x :=
  continuous_at_of_continuous_at_on_univ
    (continuous_at_within_intro
      (take ε, suppose ε > 0,
      obtain δ (Hδ : δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → dist (f x') (f x) < ε), from H this,
      exists.intro δ (and.intro
      (show δ > 0, from and.left Hδ)
      (take x' H' Hx', and.right Hδ _ Hx'))))

theorem continuous_at_dest {f : M → N} {x : M} (Hfx : continuous_at f x) :
        ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → dist (f x') (f x) < ε :=
  begin
    intro ε Hε,
    cases continuous_at_on_dest (continuous_at_on_univ_of_continuous_at Hfx) Hε with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro x' Hx',
    apply and.right Hδ,
    apply mem_univ,
    apply Hx'
  end

theorem continuous_on_intro {f : M → N} {s : set M}
        (H : ∀ x ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → dist x' x < δ → dist (f x') (f x) < ε) :
        continuous_on f s :=
  continuous_on_of_forall_continuous_at_on (λ x, continuous_at_within_intro (H x))

theorem continuous_on_dest {f : M → N} {s : set M} (H : continuous_on f s) {x : M} (Hxs : x ∈ s) :
        ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ∈ s → dist x' x < δ → dist (f x') (f x) < ε :=
  continuous_at_on_dest (continuous_at_on_of_continuous_on H Hxs)

theorem continuous_intro {f : M → N}
        (H : ∀ x ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → dist (f x') (f x) < ε) :
        continuous f :=
  continuous_of_forall_continuous_at (λ x, continuous_at_intro (H x))

theorem continuous_dest {f : M → N} (H : continuous f) (x : M) :
         ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → dist (f x') (f x) < ε :=
  continuous_at_dest (forall_continuous_at_of_continuous H x)

theorem continuous_at_of_converges_to_at {f : M → N} {x : M} (Hf : f ⟶ f x [at x]) :
  continuous_at f x :=
continuous_at_intro
(take ε, suppose ε > 0,
obtain δ Hδ, from approaches_at_dest Hf this,
exists.intro δ (and.intro
  (and.left Hδ)
  (take x', suppose dist x' x < δ,
   if Heq : x' = x then
     by rewrite [-Heq, dist_self]; assumption
   else
     (suffices dist x' x < δ, from and.right Hδ x' this Heq,
      this))))

theorem converges_to_at_of_continuous_at {f : M → N} {x : M} (Hf : continuous_at f x) :
  f ⟶ f x [at x] :=
approaches_at_intro
  (take ε, suppose ε > 0,
    obtain δ [δpos Hδ], from continuous_at_dest Hf this,
    exists.intro δ (and.intro δpos (λ x' Hx' xnex', Hδ x' Hx')))

theorem converges_seq_comp_of_converges_seq_of_cts (X : ℕ → M) [HX : converges_seq X] {f : M → N}
        (Hf : continuous f) :
        converges_seq (λ n, f (X n)) :=
  begin
    cases HX with xlim Hxlim,
    existsi f xlim,
    apply approaches_at_infty_intro,
    intros ε Hε,
    let Hcont := (continuous_at_dest (forall_continuous_at_of_continuous Hf xlim)) Hε,
    cases Hcont with δ Hδ,
    cases approaches_at_infty_dest Hxlim (and.left Hδ) with B HB,
    existsi B,
    intro n Hn,
    apply and.right Hδ,
    apply HB Hn
  end

end continuity

end metric_space

end analysis


/- complete metric spaces -/

structure complete_metric_space [class] (M : Type) extends metricM : metric_space M : Type :=
(complete : ∀ X, @analysis.cauchy M metricM X → @analysis.converges_seq M metricM X)

namespace analysis

proposition complete (M : Type) [cmM : complete_metric_space M] {X : ℕ → M} (H : cauchy X) :
  converges_seq X :=
complete_metric_space.complete X H

end analysis


/- the reals form a metric space -/

noncomputable definition metric_space_real [instance] : metric_space ℝ :=
⦃ metric_space,
  dist               := λ x y, abs (x - y),
  dist_self          := λ x, abstract by rewrite [sub_self, abs_zero] end,
  eq_of_dist_eq_zero := λ x y, eq_of_abs_sub_eq_zero,
  dist_comm          := abs_sub,
  dist_triangle      := abs_sub_le
⦄
