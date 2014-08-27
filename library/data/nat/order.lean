--- Copyright (c) 2014 Floris van Doorn. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Floris van Doorn

-- data.nat.order
-- ==============
--
-- The ordering on the natural numbers

import .basic logic.classes.decidable
import tools.fake_simplifier

using nat eq_ops tactic
using fake_simplifier
using decidable (decidable inl inr)

namespace nat


-- Less than or equal
-- ------------------

definition le (n m : ℕ) : Prop := exists k : nat, n + k = m

infix  `<=` := le
infix  `≤`  := le

theorem le_intro {n m k : ℕ} (H : n + k = m) : n ≤ m :=
exists_intro k H

theorem le_elim {n m : ℕ} (H : n ≤ m) : ∃k, n + k = m :=
H

opaque_hint (hiding le)

-- ### partial order (totality is part of less than)

theorem le_refl {n : ℕ} : n ≤ n :=
le_intro add_zero_right

theorem zero_le {n : ℕ} : 0 ≤ n :=
le_intro add_zero_left

theorem le_zero {n : ℕ} (H : n ≤ 0) : n = 0 :=
obtain (k : ℕ) (Hk : n + k = 0), from le_elim H,
add_eq_zero_left Hk

theorem not_succ_zero_le {n : ℕ} : ¬ succ n ≤ 0 :=
not_intro
  (assume H : succ n ≤ 0,
    have H2 : succ n = 0, from le_zero H,
    absurd H2 succ_ne_zero)

theorem le_trans {n m k : ℕ} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k :=
obtain (l1 : ℕ) (Hl1 : n + l1 = m), from le_elim H1,
obtain (l2 : ℕ) (Hl2 : m + l2 = k), from le_elim H2,
le_intro
  (calc
    n + (l1 + l2) =  n + l1 + l2 : add_assoc⁻¹
              ... = m + l2       : {Hl1}
              ... = k            : Hl2)

theorem le_antisym {n m : ℕ} (H1 : n ≤ m) (H2 : m ≤ n) : n = m :=
obtain (k : ℕ) (Hk : n + k = m), from (le_elim H1),
obtain (l : ℕ) (Hl : m + l = n), from (le_elim H2),
have L1 : k + l = 0, from
  add_cancel_left
    (calc
      n + (k + l) = n + k + l : add_assoc⁻¹
        ... = m + l           : {Hk}
        ... = n               : Hl
        ... = n + 0           : add_zero_right⁻¹),
have L2 : k = 0, from add_eq_zero_left L1,
calc
  n = n + 0  : add_zero_right⁻¹
... = n  + k : {L2⁻¹}
... = m      : Hk

-- ### interaction with addition

theorem le_add_right {n m : ℕ} : n ≤ n + m :=
le_intro rfl

theorem le_add_left {n m : ℕ} : n ≤ m + n :=
le_intro add_comm

theorem add_le_left {n m : ℕ} (H : n ≤ m) (k : ℕ) : k + n ≤ k + m :=
obtain (l : ℕ) (Hl : n + l = m), from (le_elim H),
le_intro
  (calc
      k + n + l  = k + (n + l) : add_assoc
             ... = k + m       : {Hl})

theorem add_le_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n + k ≤ m + k :=
add_comm ▸ add_comm ▸ add_le_left H k

theorem add_le {n m k l : ℕ} (H1 : n ≤ k) (H2 : m ≤ l) : n + m ≤ k + l :=
le_trans (add_le_right H1 m) (add_le_left H2 k)


theorem add_le_cancel_left {n m k : ℕ} (H : k + n ≤ k + m) : n ≤ m :=
obtain (l : ℕ) (Hl : k + n + l = k + m), from (le_elim H),
le_intro (add_cancel_left
  (calc
      k + (n + l)  = k + n + l : add_assoc⁻¹
               ... = k + m     : Hl))

theorem add_le_cancel_right {n m k : ℕ} (H : n + k ≤ m + k) : n ≤ m :=
add_le_cancel_left (add_comm ▸ add_comm ▸ H)

theorem add_le_inv {n m k l : ℕ} (H1 : n + m ≤ k + l) (H2 : k ≤ n) : m ≤ l :=
obtain (a : ℕ) (Ha : k + a = n), from le_elim H2,
have H3 : k + (a + m) ≤ k + l, from add_assoc ▸ Ha⁻¹ ▸ H1,
have H4 : a + m ≤ l, from add_le_cancel_left H3,
show m ≤ l, from le_trans le_add_left H4

-- add_rewrite le_add_right le_add_left

-- ### interaction with successor and predecessor

theorem succ_le {n m : ℕ} (H : n ≤ m) : succ n ≤ succ m :=
add_one ▸ add_one ▸ add_le_right H 1

theorem succ_le_cancel {n m : ℕ} (H : succ n ≤ succ m) :  n ≤ m :=
add_le_cancel_right (add_one⁻¹ ▸ add_one⁻¹ ▸ H)

theorem self_le_succ {n : ℕ} : n ≤ succ n :=
le_intro add_one

theorem le_imp_le_succ {n m : ℕ} (H : n ≤ m) : n ≤ succ m :=
le_trans H self_le_succ

theorem le_imp_succ_le_or_eq {n m : ℕ} (H : n ≤ m) : succ n ≤ m ∨ n = m :=
obtain (k : ℕ) (Hk : n + k = m), from (le_elim H),
discriminate
  (assume H3 : k = 0,
    have Heq : n = m,
      from calc
        n = n + 0   : add_zero_right⁻¹
        ... = n + k : {H3⁻¹}
        ... = m     : Hk,
    or_inr Heq)
  (take l : nat,
    assume H3 : k = succ l,
    have Hlt : succ n ≤ m, from
      (le_intro
        (calc
          succ n + l = n + succ l : add_move_succ
            ... = n + k           : {H3⁻¹}
            ... = m               : Hk)),
    or_inl Hlt)

theorem le_ne_imp_succ_le {n m : ℕ} (H1 : n ≤ m) (H2 : n ≠ m) : succ n ≤ m :=
resolve_left (le_imp_succ_le_or_eq H1) H2

theorem le_succ_imp_le_or_eq {n m : ℕ} (H : n ≤ succ m) : n ≤ m ∨ n = succ m :=
or_imp_or_left (le_imp_succ_le_or_eq H)
   (take H2 : succ n ≤ succ m, show n ≤ m, from succ_le_cancel H2)

theorem succ_le_imp_le_and_ne {n m : ℕ} (H : succ n ≤ m) : n ≤ m ∧ n ≠ m :=
obtain (k : ℕ) (H2 : succ n + k = m), from (le_elim H),
 and_intro
  (have H3 : n + succ k = m,
    from calc
      n + succ k = succ n + k : add_move_succ⁻¹
             ... = m          : H2,
    show n ≤ m, from le_intro H3)
  (assume H3 : n = m,
      have H4 : succ n ≤ n, from H3⁻¹ ▸ H,
      have H5 : succ n = n, from le_antisym H4 self_le_succ,
      show false, from absurd H5 succ_ne_self)

theorem le_pred_self {n : ℕ} : pred n ≤ n :=
case n
  (pred_zero⁻¹ ▸ le_refl)
  (take k : ℕ, (pred_succ k)⁻¹ ▸ self_le_succ)

theorem pred_le {n m : ℕ} (H : n ≤ m) : pred n ≤ pred m :=
discriminate
  (take Hn : n = 0,
    have H2 : pred n = 0,
      from calc
        pred n = pred 0 : {Hn}
           ... = 0 : pred_zero,
    H2⁻¹ ▸ zero_le)
  (take k : ℕ,
    assume Hn : n = succ k,
    obtain (l : ℕ) (Hl : n + l = m), from le_elim H,
    have H2 : pred n + l = pred m,
      from calc
        pred n + l = pred (succ k) + l   : {Hn}
               ... = k + l               : {pred_succ k}
               ... = pred (succ (k + l)) : (pred_succ (k + l))⁻¹
               ... = pred (succ k + l)   : {add_succ_left⁻¹}
               ... = pred (n + l)        : {Hn⁻¹}
               ... = pred m              : {Hl},
    le_intro H2)

theorem pred_le_imp_le_or_eq {n m : ℕ} (H : pred n ≤ m) : n ≤ m ∨ n = succ m :=
discriminate
  (take Hn : n = 0,
    or_inl (Hn⁻¹ ▸ zero_le))
  (take k : ℕ,
    assume Hn : n = succ k,
    have H2 : pred n = k,
      from calc
        pred n = pred (succ k) : {Hn}
           ... = k : pred_succ k,
    have H3 : k ≤ m, from subst H2 H,
    have H4 : succ k ≤ m ∨ k = m, from le_imp_succ_le_or_eq H3,
    show n ≤ m ∨ n = succ m, from
      or_imp_or H4
        (take H5 : succ k ≤ m, show n ≤ m, from Hn⁻¹ ▸ H5)
        (take H5 : k = m, show n = succ m, from H5 ▸ Hn))

-- ### interaction with multiplication

theorem mul_le_left {n m : ℕ} (H : n ≤ m) (k : ℕ) : k * n ≤ k * m :=
obtain (l : ℕ) (Hl : n + l = m), from (le_elim H),
have H2 : k * n + k * l = k * m, from
  calc
    k * n + k * l = k * (n + l) : by simp
              ... = k * m       : {Hl},
le_intro H2

theorem mul_le_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n * k ≤ m * k :=
mul_comm ▸ mul_comm ▸ (mul_le_left H k)

theorem mul_le {n m k l : ℕ} (H1 : n ≤ k) (H2 : m ≤ l) : n * m ≤ k * l :=
le_trans (mul_le_right H1 m) (mul_le_left H2 k)

-- mul_le_[left|right]_inv below

theorem le_decidable [instance] (n m : ℕ) : decidable (n ≤ m) :=
have general : ∀n, decidable (n ≤ m), from
  rec_on m
    (take n,
      rec_on n
        (inl le_refl)
        (take m iH, inr not_succ_zero_le))
    (take (m' : ℕ) (iH1 : ∀n, decidable (n ≤ m')) (n : ℕ),
      rec_on n
        (inl zero_le)
        (take (n' : ℕ) (iH2 : decidable (n' ≤ succ m')),
          have d1 : decidable (n' ≤ m'), from iH1 n',
          decidable.rec_on d1
            (assume Hp : n' ≤ m', inl (succ_le Hp))
            (assume Hn : ¬ n' ≤ m',
              have H : ¬ succ n' ≤ succ m', from
                assume Hle : succ n' ≤ succ m',
                  absurd (succ_le_cancel Hle) Hn,
              inr H))),
general n

-- Less than, Greater than, Greater than or equal
-- ----------------------------------------------

-- ge and gt will be transparent, so we don't need to reprove theorems for le and lt for them

definition lt (n m : ℕ) := succ n ≤ m
infix `<` := lt

abbreviation ge (n m : ℕ) := m ≤ n
infix `>=` := ge
infix `≥` := ge

abbreviation gt (n m : ℕ) := m < n
infix `>` := gt

theorem lt_def (n m : ℕ) : (n < m) = (succ n ≤ m) := refl (n < m)

-- add_rewrite gt_def ge_def --it might be possible to remove this in Lean 0.2

theorem lt_intro {n m k : ℕ} (H : succ n + k = m) : n < m :=
le_intro H

theorem lt_elim {n m : ℕ} (H : n < m) : ∃ k, succ n + k = m :=
le_elim H

theorem lt_add_succ (n m : ℕ) : n < n + succ m :=
lt_intro add_move_succ

-- ### basic facts

theorem lt_imp_ne {n m : ℕ} (H : n < m) : n ≠ m :=
and_elim_right (succ_le_imp_le_and_ne H)

theorem lt_irrefl {n : ℕ} : ¬ n < n :=
not_intro (assume H : n < n, absurd rfl (lt_imp_ne H))

theorem succ_pos {n : ℕ} : 0 < succ n :=
succ_le zero_le

theorem not_lt_zero {n : ℕ} : ¬ n < 0 :=
not_succ_zero_le

theorem lt_imp_eq_succ {n m : ℕ} (H : n < m) : exists k, m = succ k :=
discriminate
  (take (Hm : m = 0), absurd (Hm ▸ H) not_lt_zero)
  (take (l : ℕ) (Hm : m = succ l), exists_intro l Hm)

-- ### interaction with le

theorem lt_imp_le_succ {n m : ℕ} (H : n < m) : succ n ≤ m :=
H

theorem le_succ_imp_lt {n m : ℕ} (H : succ n ≤ m) : n < m :=
H

theorem self_lt_succ {n : ℕ} : n < succ n :=
le_refl

theorem lt_imp_le {n m : ℕ} (H : n < m) : n ≤ m :=
and_elim_left (succ_le_imp_le_and_ne H)

theorem le_imp_lt_or_eq {n m : ℕ} (H : n ≤ m) : n < m ∨ n = m :=
le_imp_succ_le_or_eq H

theorem le_ne_imp_lt {n m : ℕ} (H1 : n ≤ m) (H2 : n ≠ m) : n < m :=
le_ne_imp_succ_le H1 H2

theorem le_imp_lt_succ {n m : ℕ} (H : n ≤ m) : n < succ m :=
succ_le H

theorem lt_succ_imp_le {n m : ℕ} (H : n < succ m) : n ≤ m :=
succ_le_cancel H

-- ### transitivity, antisymmmetry

theorem lt_le_trans {n m k : ℕ} (H1 : n < m) (H2 : m ≤ k) : n < k :=
le_trans H1 H2

theorem le_lt_trans {n m k : ℕ} (H1 : n ≤ m) (H2 : m < k) : n < k :=
le_trans (succ_le H1) H2

theorem lt_trans {n m k : ℕ} (H1 : n < m) (H2 : m < k) : n < k :=
lt_le_trans H1 (lt_imp_le H2)

theorem le_imp_not_gt {n m : ℕ} (H : n ≤ m) : ¬ n > m :=
not_intro (assume H2 : m < n, absurd (le_lt_trans H H2) lt_irrefl)

theorem lt_imp_not_ge {n m : ℕ} (H : n < m) : ¬ n ≥ m :=
not_intro (assume H2 : m ≤ n, absurd (lt_le_trans H H2) lt_irrefl)

theorem lt_antisym {n m : ℕ} (H : n < m) : ¬ m < n :=
le_imp_not_gt (lt_imp_le H)

-- ### interaction with addition

theorem add_lt_left {n m : ℕ} (H : n < m) (k : ℕ) : k + n < k + m :=
add_succ_right ▸ add_le_left H k

theorem add_lt_right {n m : ℕ} (H : n < m) (k : ℕ) : n + k < m + k :=
add_comm ▸ add_comm ▸ add_lt_left H k

theorem add_le_lt {n m k l : ℕ} (H1 : n ≤ k) (H2 : m < l) : n + m < k + l :=
le_lt_trans (add_le_right H1 m) (add_lt_left H2 k)

theorem add_lt_le {n m k l : ℕ} (H1 : n < k) (H2 : m ≤ l) : n + m < k + l :=
lt_le_trans (add_lt_right H1 m) (add_le_left H2 k)

theorem add_lt {n m k l : ℕ} (H1 : n < k) (H2 : m < l) : n + m < k + l :=
add_lt_le H1 (lt_imp_le H2)

theorem add_lt_cancel_left {n m k : ℕ} (H : k + n < k + m) : n < m :=
add_le_cancel_left (add_succ_right⁻¹ ▸ H)

theorem add_lt_cancel_right {n m k : ℕ} (H : n + k < m + k) : n < m :=
add_lt_cancel_left (add_comm ▸ add_comm ▸ H)

-- ### interaction with successor (see also the interaction with le)

theorem succ_lt {n m : ℕ} (H : n < m) : succ n < succ m :=
add_one ▸ add_one ▸ add_lt_right H 1

theorem succ_lt_cancel {n m : ℕ} (H : succ n < succ m) :  n < m :=
add_lt_cancel_right (add_one⁻¹ ▸ add_one⁻¹ ▸ H)

theorem lt_imp_lt_succ {n m : ℕ} (H : n < m) : n < succ m
:= lt_trans H self_lt_succ

-- ### totality of lt and le

theorem le_or_gt {n m : ℕ} : n ≤ m ∨ n > m :=
induction_on n
  (or_inl zero_le)
  (take (k : ℕ),
    assume IH : k ≤ m ∨ m < k,
    or_elim IH
      (assume H : k ≤ m,
        obtain (l : ℕ) (Hl : k + l = m), from le_elim H,
        discriminate
          (assume H2 : l = 0,
            have H3 : m = k,
              from calc
                m = k + l     : Hl⁻¹
                  ... = k + 0 : {H2}
                  ... = k     : add_zero_right,
            have H4 : m < succ k, from subst  H3 self_lt_succ,
            or_inr H4)
          (take l2 : ℕ,
            assume H2 : l = succ l2,
            have H3 : succ k + l2 = m,
              from calc
                succ k + l2 = k + succ l2 : add_move_succ
                        ... = k + l       : {H2⁻¹}
                        ... = m           : Hl,
            or_inl (le_intro H3)))
      (assume H : m < k, or_inr (lt_imp_lt_succ H)))

theorem trichotomy_alt {n m : ℕ} : (n < m ∨ n = m) ∨ n > m :=
or_imp_or_left le_or_gt (assume H : n ≤ m, le_imp_lt_or_eq H)

theorem trichotomy {n m : ℕ} : n < m ∨ n = m ∨ n > m :=
iff_elim_left (or_assoc _ _ _) trichotomy_alt

theorem le_total {n m : ℕ} : n ≤ m ∨ m ≤ n :=
or_imp_or_right le_or_gt (assume H : m < n, lt_imp_le H)

theorem not_lt_imp_ge {n m : ℕ} (H : ¬ n < m) : n ≥ m :=
resolve_left le_or_gt H

theorem not_le_imp_gt {n m : ℕ} (H : ¬ n ≤ m) : n > m :=
resolve_right le_or_gt H

-- The following three theorems are automatically proved using the instance le_decidable
theorem lt_decidable [instance] (n m : ℕ) : decidable (n < m)
theorem gt_decidable [instance] (n m : ℕ) : decidable (n > m)
theorem ge_decidable [instance] (n m : ℕ) : decidable (n ≥ m)

-- Note: interaction with multiplication under "positivity"

-- ### misc

theorem strong_induction_on {P : nat → Prop} (n : ℕ) (H : ∀n, (∀m, m < n → P m) → P n) : P n :=
have H1 : ∀ {n m : nat}, m < n → P m, from
  take n,
  induction_on n
    (show ∀m, m < 0 → P m, from take m H, absurd H not_lt_zero)
    (take n',
      assume IH : ∀ {m : nat}, m < n' → P m,
      have H2: P n', from H n' @IH,
      show ∀m, m < succ n' → P m, from
        take m,
        assume H3 : m < succ n',
        or_elim (le_imp_lt_or_eq (lt_succ_imp_le H3))
          (assume H4: m < n', IH H4)
          (assume H4: m = n', H4⁻¹ ▸ H2)),
H1 self_lt_succ

theorem case_strong_induction_on {P : nat → Prop} (a : nat) (H0 : P 0)
  (Hind : ∀(n : nat), (∀m, m ≤ n → P m) → P (succ n)) : P a :=
strong_induction_on a (
  take n,
  show (∀m, m < n → P m) → P n, from
    case n
       (assume H : (∀m, m < 0 → P m), show P 0, from H0)
       (take n,
         assume H : (∀m, m < succ n → P m),
         show P (succ n), from
           Hind n (take m, assume H1 : m ≤ n, H _ (le_imp_lt_succ H1))))


-- Positivity
-- ---------
--
-- Writing "t > 0" is the preferred way to assert that a natural number is positive.

-- ### basic

theorem case_zero_pos {P : ℕ → Prop} (y : ℕ) (H0 : P 0) (H1 : ∀ {y : nat}, y > 0 → P y) : P y :=
case y H0 (take y', H1 succ_pos)

theorem zero_or_pos {n : ℕ} : n = 0 ∨ n > 0 :=
or_imp_or_left (or_swap (le_imp_lt_or_eq zero_le)) (take H : 0 = n, H⁻¹)

theorem succ_imp_pos {n m : ℕ} (H : n = succ m) : n > 0 :=
H⁻¹ ▸ succ_pos

theorem ne_zero_imp_pos {n : ℕ} (H : n ≠ 0) : n > 0 :=
or_elim zero_or_pos (take H2 : n = 0, absurd H2 H) (take H2 : n > 0, H2)

theorem pos_imp_ne_zero {n : ℕ} (H : n > 0) : n ≠ 0 :=
ne_symm (lt_imp_ne H)

theorem pos_imp_eq_succ {n : ℕ} (H : n > 0) : exists l, n = succ l :=
lt_imp_eq_succ H

theorem add_pos_right {n k : ℕ} (H : k > 0) : n + k > n :=
add_zero_right ▸ add_lt_left H n

theorem add_pos_left {n : ℕ} {k : ℕ} (H : k > 0) : k + n > n :=
add_comm ▸ add_pos_right H

-- ### multiplication

theorem mul_pos {n m : ℕ} (Hn : n > 0) (Hm : m > 0) : n * m > 0 :=
obtain (k : ℕ) (Hk : n = succ k), from pos_imp_eq_succ Hn,
obtain (l : ℕ) (Hl : m = succ l), from pos_imp_eq_succ Hm,
succ_imp_pos (calc
  n * m = succ k * m            : {Hk}
    ... = succ k * succ l       : {Hl}
    ... = succ k * l + succ k   : mul_succ_right
    ... = succ (succ k * l + k) : add_succ_right)

theorem mul_pos_imp_pos_left {n m : ℕ} (H : n * m > 0) : n > 0 :=
discriminate
  (assume H2 : n = 0,
    have H3 : n * m = 0,
      from calc
        n * m = 0 * m : {H2}
          ... = 0     : mul_zero_left,
    have H4 : 0 > 0, from H3 ▸ H,
    absurd H4 lt_irrefl)
  (take l : nat,
    assume Hl : n = succ l,
    Hl⁻¹ ▸ succ_pos)

theorem mul_pos_imp_pos_right {m n : ℕ} (H : n * m > 0) : m > 0 :=
mul_pos_imp_pos_left (mul_comm ▸ H)

-- ### interaction of mul with le and lt

theorem mul_lt_left {n m k : ℕ} (Hk : k > 0) (H : n < m) : k * n < k * m :=
have H2 : k * n < k * n + k, from add_pos_right Hk,
have H3 : k * n + k ≤ k * m, from  mul_succ_right ▸ mul_le_left H k,
lt_le_trans H2 H3

theorem mul_lt_right {n m k : ℕ} (Hk : k > 0) (H : n < m)  : n * k < m * k :=
mul_comm ▸ mul_comm ▸ mul_lt_left Hk H

theorem mul_le_lt {n m k l : ℕ} (Hk : k > 0) (H1 : n ≤ k) (H2 : m < l) : n * m < k * l :=
le_lt_trans (mul_le_right H1 m) (mul_lt_left Hk H2)

theorem mul_lt_le {n m k l : ℕ} (Hl : l > 0) (H1 : n < k) (H2 : m ≤ l) : n * m < k * l :=
le_lt_trans (mul_le_left H2 n) (mul_lt_right Hl H1)

theorem mul_lt {n m k l : ℕ} (H1 : n < k) (H2 : m < l) : n * m < k * l :=
have H3 : n * m ≤ k * m, from mul_le_right (lt_imp_le H1) m,
have H4 : k * m < k * l, from mul_lt_left (le_lt_trans zero_le H1) H2,
le_lt_trans H3 H4

theorem mul_lt_cancel_left {n m k : ℕ} (H : k * n < k * m) : n < m :=
or_elim le_or_gt
  (assume H2 : m ≤ n,
    have H3 : k * m ≤ k * n, from mul_le_left H2 k,
    absurd H3 (lt_imp_not_ge H))
  (assume H2 : n < m, H2)

theorem mul_lt_cancel_right {n m k : ℕ} (H : n * k < m * k) : n < m :=
mul_lt_cancel_left (mul_comm ▸ mul_comm ▸ H)

theorem mul_le_cancel_left {n m k : ℕ} (Hk : k > 0) (H : k * n ≤ k * m) : n ≤ m :=
have H2 : k * n < k * m + k, from le_lt_trans H (add_pos_right Hk),
have H3 : k * n < k * succ m, from mul_succ_right⁻¹ ▸ H2,
have H4 : n < succ m, from mul_lt_cancel_left H3,
show n ≤ m, from lt_succ_imp_le H4

theorem mul_le_cancel_right {n k m : ℕ} (Hm : m > 0) (H : n * m ≤ k * m) : n ≤ k :=
mul_le_cancel_left Hm (mul_comm ▸ mul_comm ▸ H)

theorem mul_cancel_left {m k n : ℕ} (Hn : n > 0) (H : n * m = n * k) : m = k :=
have H2 : n * m ≤ n * k, from H ▸ le_refl,
have H3 : n * k ≤ n * m, from H ▸ le_refl,
have H4 : m ≤ k, from mul_le_cancel_left Hn H2,
have H5 : k ≤ m, from mul_le_cancel_left Hn H3,
le_antisym H4 H5

theorem mul_cancel_left_or {n m k : ℕ} (H : n * m = n * k) : n = 0 ∨ m = k :=
or_imp_or_right zero_or_pos
  (assume Hn : n > 0, mul_cancel_left Hn H)

theorem mul_cancel_right {n m k : ℕ} (Hm : m > 0) (H : n * m = k * m) : n = k :=
mul_cancel_left Hm ((H ▸ mul_comm) ▸ mul_comm)

theorem mul_cancel_right_or  {n m k : ℕ} (H : n * m = k * m) : m = 0 ∨ n = k :=
mul_cancel_left_or ((H ▸ mul_comm) ▸ mul_comm)

theorem mul_eq_one_left {n m : ℕ} (H : n * m = 1) : n = 1 :=
have H2 : n * m > 0, from H⁻¹ ▸ succ_pos,
have H3 : n > 0, from mul_pos_imp_pos_left H2,
have H4 : m > 0, from mul_pos_imp_pos_right H2,
or_elim le_or_gt
  (assume H5 : n ≤ 1,
    show n = 1, from le_antisym H5 H3)
  (assume H5 : n > 1,
    have H6 : n * m ≥ 2 * 1, from mul_le H5 H4,
    have H7 : 1 ≥ 2, from mul_one_right ▸ H ▸ H6,
    absurd self_lt_succ (le_imp_not_gt H7))

theorem mul_eq_one_right {n m : ℕ} (H : n * m = 1) : m = 1 :=
mul_eq_one_left (mul_comm ▸ H)

end nat
