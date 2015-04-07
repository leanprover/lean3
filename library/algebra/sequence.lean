import data.nat data.int data.subtype algebra.ordered_field init.quot --logic.axioms.funext
open nat algebra eq eq.ops 

/-context

  parameter A : Type
  parameters (a : A) (s : A → A)
  definition foo (n : ℕ) : A := nat.rec_on n a (λn' IH, s IH)
  local attribute foo  [coercion]
end-/

constant prerat : Type.{1}
inductive rat : Type.{1} :=
| wrap : prerat → rat

notation `ℚ` := rat

axiom rat_is_lof : discrete_linear_ordered_field ℚ

-- this disappeared from order at the last commit??
theorem lt_of_lt_of_eq {A : Type} [s : has_lt A] {a b c : A} (H1 : a < b) (H2 : b = c) : a < c := sorry

section rat

definition rat.is_lin_ord [instance] : discrete_linear_ordered_field ℚ := rat_is_lof

-- the following are needed for dealing with numerals and coercions to ℚ.

definition nat.to_rat [reducible] [coercion] (n : ℕ) : ℚ :=
nat.rec_on n (0 : ℚ) (λ k : ℕ, λ to_rat_n : ℚ, to_rat_n + (1 : ℚ))

definition q0 [reducible] := (0 : ℚ)
definition q1 [reducible] := (1 : ℚ)

theorem add_halves_helper (a : ℚ) : a / 2 + a / 2 = a :=
  calc
    a / 2 + a / 2 = a / (q0 + q1 + q1) + a / (q0 + q1 + q1) : !refl
    ... = a / (q1 + q1) + a / (q1 + q1) : (zero_add q1) ▸ !refl
    ... = a : add_halves

theorem rnip_helper (n : ℕ) (Hn : (nat.to_rat n) ≥ 0) : (nat.to_rat (succ n)) ≥ 0 := 
  have H : nat.to_rat n + 1 = (nat.to_rat (succ n)), from !refl,
  H⁻¹ ▸ (algebra.add_nonneg Hn (algebra.le_of_lt algebra.zero_lt_one))

theorem rat_of_nat_is_pos (n : ℕ) (Hn : n > 0) : nat.to_rat n > 0 :=
  have Hn' : ∃ k, n = succ k, from exists_eq_succ_of_pos Hn,
  exists.elim Hn' (take l, take Hl : n = succ l,
    have Hl' : nat.to_rat l ≥ 0, from  nat.induction_on l !algebra.le.refl (λ a H, rnip_helper a H),
    have Hl'' : (nat.to_rat l) + 1 > 0, from algebra.lt_add_of_le_of_pos Hl' (algebra.zero_lt_one),
    calc
      nat.to_rat n = nat.to_rat (succ l) : Hl
               ... > 0                   : Hl'')

theorem rat_div_nat_pos {a : ℚ} {n : ℕ} (H : a > 0) (Hn : n > 0) : a / n > 0 := 
  pos_div_of_pos_of_pos H (rat_of_nat_is_pos n Hn)


-- define sequences and operations on sequences

definition rat_sequence [reducible] := ℕ → ℚ

definition add (s t : rat_sequence) : rat_sequence :=
  λ n : ℕ, s n + t n
infix `+` := add

definition neg (s : rat_sequence) : rat_sequence :=
  λ n : ℕ, - (s n)
prefix `-` := neg

theorem neg_neg_seq {s : rat_sequence} : - - s = s :=
  funext (take n : ℕ, !neg_neg ▸ !refl)

theorem neg_seq_component {s : rat_sequence} (n : ℕ) : - ((- s) n) = (s n) :=
  have H : (- s) n = - (s n), from !refl, !neg_neg ▸ ((iff.mp' !neg_eq_neg_iff_eq) H)

definition sub [reducible] (s t : rat_sequence) : rat_sequence :=
  s + (- t)
infix `-` := sub

theorem seq_sub_self (s : rat_sequence) : s - s = λ n, 0 := 
  funext (take x,
    show s x - s x = 0, from !algebra.sub_self)

definition vanishes (s : rat_sequence) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → abs (s n) < ε

definition converges_to (s : rat_sequence) (a : ℚ) : Prop :=
  vanishes (λ n, s n - a)

definition converges (s : rat_sequence) : Prop :=
  ∃ a : ℚ, converges_to s a

definition converge_to_same (s t : rat_sequence) : Prop :=
  ∃ a : ℚ, converges_to s a ∧ converges_to t a

definition cauchy (s : rat_sequence) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N : ℕ, ∀ m n : ℕ, m ≥ N → n ≥ N → abs (s m - s n) < ε

theorem abs_add_le_add_abs (x y : ℚ) : abs (x + y) ≤ abs x + abs y :=
  have H [visible] :  abs (x + y) - abs (x) ≤ abs (x + y - x), from !abs_sub_abs_le_abs_sub,
  begin
    rewrite [{x + y}algebra.add.comm at H, add_neg_cancel_right at H, {y + x}algebra.add.comm at H], 
    apply (iff.mp' (!le_add_iff_sub_left_le)),
    exact H
  end

theorem sum_vanishes_of_vanishes (s t : rat_sequence) (Hs : vanishes s) (Ht : vanishes t) :
    vanishes (s + t) :=
  begin
    rewrite [↑vanishes, ↑vanishes at Hs, ↑vanishes at Ht],
    intro ε, intro H,
    have Hs' : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → abs (s n) < ε / 2, from Hs (ε / 2) (rat_div_nat_pos H (zero_lt_succ 1)),
    have Ht' : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → abs (t n) < ε / 2, from Ht (ε / 2) (rat_div_nat_pos H (zero_lt_succ 1)),
    apply exists.elim,
      exact Hs',
      intro a, intro Ha,
      apply exists.elim,
        exact Ht',
        intro b, intro Hb,
        fapply exists.intro,
          exact (max a b),
          intro n, intro Hn,
          rewrite ↑add,
          apply algebra.lt_of_le_of_lt,
          exact !abs_add_le_add_abs,
        apply algebra.lt.trans,
        apply algebra.add_lt_add_right,
        have Han : n ≥ a, from algebra.le.trans (!max.left) Hn,
        exact (Ha n Han),
      apply lt_of_lt_of_eq,
      apply algebra.add_lt_add_left,
      have Hbn : n ≥ b, from algebra.le.trans (!max.right) Hn,
      exact (Hb n Hbn),
    exact (add_halves_helper ε)
  end

theorem sum_converges_of_converges (s t : rat_sequence) (a b : ℚ) (Hs : converges_to s a) 
    (Ht : converges_to t b) : converges_to (s + t) (a + b) :=
  begin
    rewrite [↑converges_to, ↑converges_to at Hs, ↑converges_to at Ht],
    have H : vanishes (add (λ n, s n - a) (λ n, t n - b)), from (sum_vanishes_of_vanishes _ _ Hs Ht),
    rewrite [↑vanishes, ↑vanishes at H],
    intro ε, intro H1,
    apply exists.elim,
      exact (H ε H1),
      intro a1, intro Ha1,
      fapply exists.intro,
        exact a1,
        intro n, intro Hn,
        have H' : abs (add (λ k, s k - a) (λ k, t k - b) n) < ε, from Ha1 n Hn,
        have H'' : abs ((s n - a) + (t n - b)) < ε, from H',
        rewrite [algebra.add.assoc at H'', {-a+_}algebra.add.comm at H'', 
          algebra.add.assoc at H'', -(algebra.add.assoc (s n)) at H'', -neg_add_rev at H''],
        exact H''
    end

theorem sub_dist (a b c d : ℚ) : (a + b) - (c + d) = a + b - c - d :=
  !sub_add_eq_sub_sub

theorem cauchy_of_converges (s : rat_sequence) (H : converges s) : cauchy s :=
  begin
    rewrite [↑cauchy, ↑converges at H, ↑converges_to at H],
    intro ε, intro He,
    apply exists.elim,
      exact H,
      intro a, intro Ha,
      rewrite ↑vanishes at Ha,
      have Hb : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → abs (s n - a) < ε / 2, from Ha (ε / 2) (rat_div_nat_pos He (zero_lt_succ 1)),
      apply exists.elim,
        exact Hb,
        intro N, intro HN,
        fapply exists.intro,
          exact N,
          intro m, intro n, intro Hm, intro Hn,
          have HNm : abs (s m - a) < ε / 2, from HN m Hm,
          have HNn : abs (a - s n) < ε / 2, from !abs_sub ▸ (HN n Hn),
          rewrite [ -(add_sub_add_left_eq_sub _ _ a), sub_dist, {a+_}algebra.add.comm, 2 algebra.add.assoc, 
            -(algebra.add.assoc a), {a+_}algebra.add.comm, algebra.add.assoc, -algebra.add.assoc (s m)],
          apply lt_of_lt_of_eq, -- algebra.
          rotate_left 1,
          apply (add_halves_helper ε),
          apply algebra.lt_of_le_of_lt,
          rotate_left 1,
          apply (algebra.add_lt_add HNm HNn),
          apply abs_add_le_add_abs
  end

/-definition cauchy_sequence [reducible] := {s : rat_sequence | cauchy s}

definition cauchy.to_rat [reducible] [coercion] (s : cauchy_sequence) : rat_sequence :=
  subtype.rec_on s (λ t H, t)

definition cauchy.equiv (s t : cauchy_sequence) : Prop :=
   ∀ ε : ℚ, ∃ N : ℕ, ∀ m n : ℕ, m ≥ N → n ≥ N → abs (cauchy.to_rat s n - cauchy.to_rat t m) < ε

notation p `≡` q := cauchy.equiv p q

check λ p : cauchy_sequence, λ n : ℕ, p n-/

--definition seq.equiv (s t : rat_sequence) : Prop := cauchy (s - t)
definition seq.equiv (s t : rat_sequence) : Prop :=
  vanishes (s - t)-- ∀ ε : ℚ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → abs (s n - t n) < ε
notation p `≡` q := seq.equiv p q

-- show seq.equiv is an equivalence relation

theorem seq.equiv.refl (s : rat_sequence) : s ≡ s :=
  begin
    rewrite [↑seq.equiv, ↑vanishes, ↑sub],
    intros [ε, Hε],
    fapply exists.intro,
      exact 0,
      rewrite seq_sub_self,
      intros [n, Hn],
      rewrite abs_zero,
      exact Hε
  end

theorem seq.equiv.symm {s t : rat_sequence} (H : s ≡ t) : t ≡ s :=
  begin
    rewrite [↑seq.equiv at *, ↑vanishes at *],
    intros [ε, Hε],
    have H' : ∃ N, ∀ n, n ≥ N → abs (sub s t n) < ε, from H ε Hε,
    apply (exists.elim H'),
    intros [a, Ha],
    fapply exists.intro,
    exact a,
    intros [n, Hn],
    have H'' : abs (sub s t n) < ε, from (Ha n Hn),
    rewrite [↑sub at *, ↑add at *, -abs_neg, neg_add, algebra.add.comm, neg_seq_component],
    exact H''
  end

theorem seq.equiv.trans {r s t : rat_sequence} (H1 : r ≡ s) (H2 : s ≡ t) : r ≡ t :=
  begin
    rewrite [↑seq.equiv at *, ↑vanishes at *],
    intros [ε, Hε],
    have H1' : ∃ N, ∀ n, n ≥ N → abs (sub r s n) < ε / 2, from H1 (ε / 2) (rat_div_nat_pos Hε (zero_lt_succ 1)),
    have H2' : ∃ N, ∀ n, n ≥ N → abs (sub s t n) < ε / 2, from H2 (ε / 2) (rat_div_nat_pos Hε (zero_lt_succ 1)),
    apply exists.elim,
      exact H1',
      intros [a, Ha],
      apply exists.elim,
        exact H2',
        intros [b, Hb],
        fapply exists.intro,
          exact (max a b),
          intros [n, Hn],
          apply lt_of_lt_of_eq, --algebra.
          rotate_left 1,
          exact (add_halves_helper ε),
          rewrite [↑sub at *, ↑add at *],
          apply algebra.lt_of_le_of_lt,
          rewrite [-(algebra.add_zero (r n)), -(algebra.sub_self (s n)), add.comm (s n), 
            -algebra.add.assoc, algebra.add.assoc],
          apply abs_add_le_add_abs,
          apply algebra.add_lt_add,
          have Han : n ≥ a, from algebra.le.trans !max.left Hn,
          exact (Ha n Han),
          have Hbn : n ≥ b, from algebra.le.trans !max.right Hn,
          exact (Hb n Hbn)
  end


definition cauchy_sequence [reducible] := {s : rat_sequence | cauchy s}

definition cauchy.to_rat [reducible] [coercion] (s : cauchy_sequence) : rat_sequence :=
  subtype.rec_on s (λ t H, t)

-- show setoid cauchy_sequence

definition cauchy.equiv [reducible] (s t : cauchy_sequence) : Prop :=
  seq.equiv (cauchy.to_rat s) (cauchy.to_rat t)

theorem cauchy.equiv.refl (s : cauchy_sequence) : cauchy.equiv s s :=
  seq.equiv.refl (cauchy.to_rat s)

theorem cauchy.equiv.symm (s t : cauchy_sequence) (H : cauchy.equiv s t) : cauchy.equiv t s :=
  seq.equiv.symm H

theorem cauchy.equiv.trans (r s t : cauchy_sequence) (H1 : cauchy.equiv r s) (H2 : cauchy.equiv s t) : cauchy.equiv r t :=
  seq.equiv.trans H1 H2

theorem cauchy.equiv.is_equiv : equivalence cauchy.equiv := 
  mk_equivalence cauchy.equiv cauchy.equiv.refl cauchy.equiv.symm cauchy.equiv.trans

definition cauchy.to_setoid [instance] : setoid cauchy_sequence :=
  ⦃setoid, r := cauchy.equiv, iseqv := cauchy.equiv.is_equiv ⦄

definition real := quot cauchy.to_setoid

theorem add.well_defined (q r s t : cauchy_sequence) (H1 : cauchy.equiv q r) (H2 : cauchy.equiv s t) :
    q + s = r + t := sorry

example (x : real) : x = x :=
  begin
  end

end rat
