import data.nat data.subtype algebra.ordered_field
open nat algebra eq eq.ops

inductive rat : Type
axiom rat_is_lof : discrete_linear_ordered_field rat
notation `ℚ` := rat

--axiom nat_is_rat (n : ℕ) : rat
--definition nat.to_rat [coercion] (n : ℕ) : rat :=  nat_is_rat n

section rat

definition rat.is_lin_ord [instance] : discrete_linear_ordered_field ℚ := rat_is_lof

-- the following are needed for dealing with numerals and coercions to ℚ.

definition nat.to_rat [reducible] [coercion] (n : ℕ) : ℚ :=
  nat.rec_on n 0 (λ k : ℕ, λ to_rat_n : rat, to_rat_n + (typeof 1 : ℚ))

definition q0 [reducible] := (typeof 0 : ℚ)
definition q1 [reducible] := (typeof 1 : ℚ)

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
      ... = (nat.to_rat l) + 1 : refl
      ... > 0 : Hl'')

theorem rat_div_nat_pos {a : ℚ} {n : ℕ} (H : a > 0) (Hn : n > 0) : a / n > 0 := 
  pos_div_of_pos_of_pos H (rat_of_nat_is_pos n Hn)


-- define sequences and operations on sequences

structure sequence (A : Type) :=
  mk :: (seq : ℕ → A)

check ⦃ sequence, seq := λ n : ℕ, nat.to_rat n⦄

definition rat_sequence := ℕ → ℚ

definition add (s t : rat_sequence) : rat_sequence :=
  λ n : ℕ, s n + t n
infix `+` := add

definition neg (s : rat_sequence) : rat_sequence :=
  λ n : ℕ, - (s n)
prefix `-` := neg

definition sub [reducible] (s t : rat_sequence) : rat_sequence :=
  s + (- t)
infix `-` := sub

theorem seq_sub_self (s : rat_sequence) : s - s = λ n, 0 := 
  have H : s - s = (λ n : ℕ, s n + -s n) , from
    begin
      rewrite [↑sub, ↑add, ↑neg]
    end,
  have H' : s - s = (λ n : ℕ, 0), from algebra.sub_self (s n) ▸ H,
  sorry

definition vanishes (s : rat_sequence) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → abs (s n) < ε

definition converges_to (s : rat_sequence) (a : ℚ) : Prop :=
  vanishes (λ n, s n - a)

definition converges (s : rat_sequence) : Prop :=
  ∃ a : ℚ, converges_to s a

definition converge_to_same (s t : rat_sequence) : Prop :=
  ∃ a : ℚ, converges_to s a ∧ converges_to t a
--local notation p `≡` q := converge_to_same p q

definition cauchy (s : rat_sequence) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N : ℕ, ∀ m n : ℕ, m ≥ N → n ≥ N → abs (s m - s n) < ε

--definition cauchy_equiv (s t : rat_sequence) (Cs : cauchy s) (Ct : cauchy t) : Prop :=
--  converge_to_same s t

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
      apply algebra.lt_of_lt_of_eq,
      apply algebra.add_lt_add_left,
      have Hbn : n ≥ b, from algebra.le.trans (!max.right) Hn,
      exact (Hb n Hbn),
    have H2 : ε / 2 + ε / 2 = ε, from add_halves_helper ε,
    exact H2
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

definition cauchy_sequence := {s : rat_sequence | cauchy s}

definition rat_seq.to_cauchy_seq [reducible] [coercion] (s : cauchy_sequence) : rat_sequence :=
  subtype.rec_on s (λ t H, t)

definition seq.equiv (s t : rat_sequence) : Prop := vanishes (s - t)
notation p `≡` q := seq.equiv p q

-- show seq.equiv is an equivalence relation
theorem seq.equiv.refl {s : rat_sequence} : s ≡ s :=
  begin
    rewrite [↑seq.equiv, ↑vanishes],
    intro ε, intro H,
    fapply exists.intro,
      exact 0,
      intro n, intro Hn,
      rewrite [seq_sub_self, abs_zero],
      exact H
  end

-- wrong approach below. want: two (cauchy) seqs are equivalent if their difference vanishes.

/-definition cauchy_equiv (s t : cauchy_sequence) := converge_to_same (rat_seq.to_cauchy_seq s) (rat_seq.to_cauchy_seq t)
notation p `≡` q := cauchy_equiv p q

-- show cauchy_equiv is an equivalence relation.
theorem cauchy_equiv.refl {s : cauchy_sequence} : s ≡ s :=
  begin
    rewrite ↑cauchy_equiv,
    fapply exists.intro,
    have s' : rat_sequence, from rat_seq.to_cauchy_seq s,
    rewrite ↑rat_sequence,
  end
 -/ 
end rat

