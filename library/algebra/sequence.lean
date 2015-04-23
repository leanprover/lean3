import data.nat data.int data.subtype algebra.ordered_field init.quot data.list  --logic.axioms.funext
open nat algebra eq eq.ops list
namespace sequence
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

section rat

definition rat.is_lin_ord [instance] : discrete_linear_ordered_field ℚ := rat_is_lof

---------------------------
-- These belong elsewhere

--why doesn't this exist?
theorem le_of_eq {a b : ℚ} (H1 : a = b) : a ≤ b :=
  algebra.le_of_not_lt (take H : b < a, absurd !rfl (H1 ▸ (algebra.ne_of_lt H)))

--------------------

-- the following are needed for dealing with numerals and coercions to ℚ.

definition nat.to_rat [reducible] [coercion] (n : ℕ) : ℚ :=
nat.rec_on n (0 : ℚ) (λ k : ℕ, λ to_rat_n : ℚ, to_rat_n + (1 : ℚ))

definition q0 [reducible] := (0 : ℚ)
definition q1 [reducible] := (1 : ℚ)

--.45 sec
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
local infix `+` := add

definition neg (s : rat_sequence) : rat_sequence :=
  λ n : ℕ, - (s n)
local prefix `-` := neg

theorem neg_neg_seq {s : rat_sequence} : - - s = s :=
  funext (take n : ℕ, !neg_neg ▸ !refl)

theorem neg_seq_component {s : rat_sequence} (n : ℕ) : - ((- s) n) = (s n) :=
  have H : (- s) n = - (s n), from !refl, !neg_neg ▸ ((iff.mp' !neg_eq_neg_iff_eq) H)

definition sub [reducible] (s t : rat_sequence) : rat_sequence :=
  s + (- t)
local infix `-` := sub

theorem seq_sub_self (s : rat_sequence) : s - s = λ n, 0 :=
  funext (take x,
    show s x - s x = 0, from !algebra.sub_self)

definition mul [reducible] (s t : rat_sequence) : rat_sequence :=
  λ n : ℕ, (s n) * (t n)
local infix `*` := mul

definition inv [reducible] (s : rat_sequence) : rat_sequence :=
  λ n : ℕ, 1 / (s n)
local postfix `⁻¹` := inv

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

definition bounded [reducible] (s : rat_sequence) : Prop := ∃ M : ℚ, ∀ n : ℕ, abs (s n) ≤ M

theorem sum_vanishes_of_vanishes (s t : rat_sequence) (Hs : vanishes s) (Ht : vanishes t) :
    vanishes (s + t) :=
  begin
    rewrite ↑vanishes at *,
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
          exact !abs_add_le_abs_add_abs,
        apply algebra.lt.trans,
        apply algebra.add_lt_add_right,
        have Han : a ≤ n, from le.trans (!le_max_left) Hn,
        exact (Ha n Han),
        rewrite -(add_halves_helper ε) at {2},
        apply algebra.add_lt_add_left,
        have Hbn : n ≥ b, from le.trans (!le_max_right) Hn,
        exact (Hb n Hbn)
  end

theorem sum_converges_of_converges (s t : rat_sequence) (a b : ℚ) (Hs : converges_to s a)
    (Ht : converges_to t b) : converges_to (s + t) (a + b) :=
  begin
    rewrite ↑converges_to at *,
    have H : vanishes (add (λ n, s n - a) (λ n, t n - b)), from (sum_vanishes_of_vanishes _ _ Hs Ht),
    rewrite ↑vanishes at *,
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
----
-- Prove all cauchy seqs are bounded
----

-- create list of nats from 0 to N - 1
definition nat_list : ℕ → list ℕ
  | 0 := [0]
  | (succ n) := cons n (nat_list n)

theorem in_nat_list : ∀{N : ℕ}, ∀ {n}, n < N → n ∈ nat_list N
  | 0 n Hn := absurd Hn !not_lt_zero
  | (succ a) n Hn := begin
      apply (or.elim (nat.lt_or_eq_of_le (le_of_lt_succ Hn))),
        intro Ho,
        apply mem_cons_of_mem,
        apply (in_nat_list Ho),
        intro Ho,
        rewrite Ho,
        apply mem_cons
    end

definition rat_list_max : list ℚ → ℚ  -- default if l is empty, else max l
  | []        := 0
  | [h]       := abs h
  | (h :: t)  := algebra.max (abs h) (rat_list_max t)

theorem rat_list_max_of_singleton (h : ℚ) : rat_list_max [h] = abs h := rfl

theorem lt_rat_list_max_of_in_rat_list : ∀{l : list ℚ}, ∀{q : ℚ}, q ∈ l → abs q ≤ rat_list_max l
  | []               q Hq  :=  absurd Hq !not_mem_nil
  | [h]              q Hq  :=
    have H1 : q = h, from mem_singleton Hq,
     le_of_eq (H1⁻¹ ▸ !rat_list_max_of_singleton)
  | (h :: (h' :: t)) q Hq  :=
    or.elim (iff.mp !mem_cons_iff Hq)
      (assume H1 : q = h,
        calc
          rat_list_max (h :: (h' :: t)) = algebra.max (abs h) (rat_list_max (h' :: t)) : rfl
                                    ... ≥ abs h : algebra.max.left
                                    ... = abs q : H1)
      (assume H1 : q ∈ (h' :: t),
        calc
          rat_list_max (h :: (h' :: t)) = algebra.max (abs h) (rat_list_max (h' :: t)) : rfl
                                    ... ≥ rat_list_max (h' :: t) : algebra.max.right
                                    ... ≥ abs q : lt_rat_list_max_of_in_rat_list H1)

-- return max of first n values of rat seq
definition max_init_seq (s : rat_sequence) (N : ℕ) : ℚ :=
  rat_list_max (map s (nat_list N))

theorem lt_seq_max (s : rat_sequence) (N : ℕ) (a : ℕ) (Ha : a < N) : abs (s a) ≤ max_init_seq s N :=
  have H : mem (s a) (map s (nat_list N)), by apply mem_map; apply (in_nat_list Ha),
  lt_rat_list_max_of_in_rat_list H


--.13 sec
theorem bounded_of_cauchy {s : rat_sequence} (H : cauchy s) : bounded s :=
  begin
  rewrite [↑bounded, ↑cauchy at H],
  apply exists.elim,
    exact (H 1 algebra.zero_lt_one),
    intros [N, HN],
    fapply exists.intro,
      exact (algebra.max (max_init_seq s N) (abs (s N) + 1)),
      intro n,
      have em : n < N ∨ ¬(n < N), from !decidable.em,
      apply (or.elim em),
        intro Hn,
        apply algebra.le.trans,
        exact (lt_seq_max s N n Hn),
        apply algebra.max.left,
        intro Hn,
        apply algebra.le.trans,
         rotate_left 1,
          apply algebra.max.right,
          have HNn : n ≥ N, from algebra.le_of_not_lt Hn,
          have Ha : abs (s n - s N) < 1, from HN n N HNn (le.refl N),
          apply (iff.mp' !le_add_iff_sub_left_le),
          apply (le_of_lt (calc
            abs (s n) - abs (s N) ≤ abs (s n - s N) : abs_sub_abs_le_abs_sub
            ... < 1 : Ha))
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
      have Hb : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → abs (s n - a) < ε / 2,
        from Ha (ε / 2) (rat_div_nat_pos He (zero_lt_succ 1)),
      apply exists.elim,
        exact Hb,
        intro N, intro HN,
        fapply exists.intro,
          exact N,
          {intro m, intro n, intro Hm, intro Hn,
          have HNm : abs (s m - a) < ε / 2, from HN m Hm,
          have HNn : abs (a - s n) < ε / 2, from !abs_sub ▸ (HN n Hn),
          rewrite [ -(add_sub_add_left_eq_sub _ _ a), sub_dist, {a+_}algebra.add.comm, 2 algebra.add.assoc,
            -(algebra.add.assoc a), {a+_}algebra.add.comm, algebra.add.assoc, -algebra.add.assoc (s m)],
          rewrite -(add_halves_helper ε),
          apply algebra.lt_of_le_of_lt,
          apply abs_add_le_abs_add_abs,
          apply algebra.add_lt_add,
          exact HNm,
          exact HNn}
  end

-- classical-ish?
theorem nonzero_of_not_vanishes (s : rat_sequence) (H : cauchy s) (Hv : ¬vanishes s) :
        ∃ B N : ℕ, ∀ n : ℕ, n > N → abs (s n) < B := sorry
/-  begin
    rewrite [↑cauchy at *, ↑vanishes at *],
  end-/

definition seq.equiv (s t : rat_sequence) : Prop :=
  vanishes (s - t)


-- show seq.equiv is an equivalence relation

theorem seq.equiv.refl (s : rat_sequence) : seq.equiv s s :=
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

theorem seq.equiv.symm {s t : rat_sequence} (H : seq.equiv s t) : seq.equiv t s :=
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

theorem seq.equiv.trans {r s t : rat_sequence} (H1 : seq.equiv r s) (H2 : seq.equiv s t) : seq.equiv r t :=
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
          rewrite -(add_halves_helper ε),
          apply algebra.lt_of_le_of_lt,
          rewrite [↑sub at *, ↑add at *, -(algebra.add_zero (r n)), -(algebra.sub_self (s n)), add.comm (s n),
            -algebra.add.assoc, algebra.add.assoc],
          apply abs_add_le_abs_add_abs,
          apply algebra.add_lt_add,
          have Han : n ≥ a, from le.trans !le_max_left Hn,
          exact (Ha n Han),
          have Hbn : n ≥ b, from le.trans !le_max_right Hn,
          exact (Hb n Hbn)
  end
end rat



section cauchy

record cauchy_sequence : Type :=
  (seq : rat_sequence) (is_cauchy : cauchy seq)


definition cauchy.to_rat [reducible] (s : cauchy_sequence) : ℕ → ℚ :=
  cauchy_sequence.seq s

local attribute cauchy.to_rat [coercion]

----
-- cauchy is preserved under add, sub, mul
----

theorem add_cauchy_of_cauchy (s t : cauchy_sequence) : cauchy (s + t) :=
  begin
    have Hs : cauchy s, from cauchy_sequence.is_cauchy s,
    have Ht : cauchy t, from cauchy_sequence.is_cauchy t,
    rewrite ↑cauchy at *,
    intros [ε, Hε],
    apply exists.elim,
      exact (Hs (ε / 2) (rat_div_nat_pos Hε (zero_lt_succ 1))),
      intros [a, Ha],
      apply exists.elim,
        exact (Ht (ε / 2) (rat_div_nat_pos Hε (zero_lt_succ 1))),
        intros [b, Hb],
        fapply exists.intro,
        exact (max a b),
        intros [m, n, Hm, Hn],
        rewrite [↑add, {s n + _}algebra.add.comm, sub_add_eq_sub_sub, (algebra.add.assoc (s m)),
        algebra.add.comm, -algebra.add.assoc],
        apply algebra.lt_of_le_of_lt,
        apply abs_add_le_abs_add_abs,
        rewrite -(add_halves_helper ε),
        apply algebra.add_lt_add,
        rewrite algebra.add.comm,
        exact (Ha _ _ (nat.le.trans !le_max_left Hm) (nat.le.trans !le_max_left Hn)),
        exact (Hb _ _ (nat.le.trans !le_max_right Hm) (nat.le.trans !le_max_right Hn))
  end

theorem neg_cauchy_of_cauchy (s : cauchy_sequence) : cauchy (- s) :=
  begin
    have Hs : cauchy s, from cauchy_sequence.is_cauchy s,
    rewrite ↑cauchy at *,
    intros [ε, Hε],
    have Hs': ∃ N, ∀ m n, m ≥ N → n ≥ N → abs (s m - s n) < ε, from Hs ε Hε,
    apply exists.elim,
    exact Hs',
    intros [a, Ha],
    fapply exists.intro,
    exact a,
    intros [m, n, Hm, Hn],
    rewrite [-abs_neg, neg_sub, ↑algebra.sub, neg_seq_component, algebra.add.comm],
    exact (Ha _ _ Hm Hn)
  end

theorem add_lt_add_of_lt_of_lt {a b c d : ℚ} (H1 : a < b) (H2 : c < d) : a + c < b + d := sorry

theorem abs_eq_zero_of_abs_le_zero {a : ℚ} (H : abs a ≤ 0) : abs a = 0 := sorry

theorem pos_div_helper {ε N : ℚ} (Hε : ε > 0) (HN : N > 0) : ε / ((2 : ℚ) * N) > 0 := sorry

theorem sub_cauchy_of_cauchy (s t : cauchy_sequence) : cauchy (s - t) :=
  add_cauchy_of_cauchy (s) (cauchy_sequence.mk (-t) (neg_cauchy_of_cauchy t))

-- uses nonzero_of_not_vanishes
theorem inv_cauchy_of_nonzero_cauchy (s : cauchy_sequence) (Hs : ¬vanishes s) : cauchy s⁻¹ :=
  sorry
  /-begin
    have Cs : cauchy s, from cauchy_sequence.is_cauchy s,
    rewrite [↑cauchy at *, ↑vanishes at *],
  end-/

-- helper lemmas for following
lemma mul_cauchy_helper_1 (s t : cauchy_sequence) (ε : ℚ) (Ns : ℚ) (HNs : ∀ n, abs (s n) ≤ Ns)
                           (Hε : ε > 0) (Nseq0 : Ns = (0: ℚ))
      : (∃ (N : ℕ), ∀ (m n : ℕ), m ≥ N → n ≥ N → abs (s m * t m - s n * t n) < ε) :=
  begin
    fapply exists.intro, exact 0, intros [m, n, Hm, Hn],
    have H0 : ∀ k, abs (s k) = 0, from (take k, abs_eq_zero_of_abs_le_zero (Nseq0 ▸ (HNs k))),
    apply (calc
      abs (s m * t m - s n * t n) ≤ abs (s m * t m) + abs (-(s n * t n)) : abs_add_le_abs_add_abs
      ... = abs (s m) * abs (t m) + abs (s n) * abs (t n) : by rewrite [abs_neg, 2 abs_mul]
      ... = 0 : by rewrite [2 H0, 2 algebra.zero_mul, algebra.zero_add]
      ... < ε : Hε)
  end

lemma mul_cauchy_helper_2 (s t : cauchy_sequence) (ε : ℚ) (Nt : ℚ) (HNt : ∀ n, abs (t n) ≤ Nt)
                           (Hε : ε > 0) (Nteq0 : Nt = (0: ℚ))
      : (∃ (N : ℕ), ∀ (m n : ℕ), m ≥ N → n ≥ N → abs (s m * t m - s n * t n) < ε) :=
  begin
    fapply exists.intro, exact 0, intros [m, n, Hm, Hn],
    have H0 : ∀ k, abs (t k) = 0, from (take k, abs_eq_zero_of_abs_le_zero (Nteq0 ▸ (HNt k))),
    apply (calc
      abs (s m * t m - s n * t n) ≤ abs (s m * t m) + abs (-(s n * t n)) : abs_add_le_abs_add_abs
      ... = abs (s m) * abs (t m) + abs (s n) * abs (t n) : by rewrite [abs_neg, 2 abs_mul]
      ... = 0 : by rewrite [2 H0, 2 algebra.mul_zero, algebra.zero_add]
      ... < ε : Hε)
  end

lemma mul_cauchy_helper_3 (s t : cauchy_sequence) (Hs : cauchy s) (Ht : cauchy t) (ε : ℚ) (Ns Nt : ℚ)
                           (HNs : ∀ n, abs (s n) ≤ Ns) (HNt : ∀ n, abs (t n) ≤ Nt)
                           (Hε : ε > 0) (Nsge0 : Ns > (0 : ℚ)) (Ntge0 : Nt > (0: ℚ))
      : (∃ (N : ℕ), ∀ (m n : ℕ), m ≥ N → n ≥ N → abs (s m * t m - s n * t n) < ε) :=
  begin
    apply exists.elim, exact (Hs (ε / ((2 : ℚ) * Nt)) (pos_div_helper Hε Ntge0)), intros [Sε, HSε],
    apply exists.elim, exact (Ht (ε / ((2 : ℚ) * Ns)) (pos_div_helper Hε Nsge0)), intros [Tε, HTε],
    fapply exists.intro,
    exact (max Sε Tε),
    intros [m, n, Hm, Hn],
    rewrite [-algebra.add_zero (s m * t m), -algebra.sub_self (s m * t n), algebra.add.comm (s m * t n),
      -algebra.add.assoc, algebra.add.assoc, -algebra.mul_sub_left_distrib,
      -algebra.mul_sub_right_distrib],
    have HTε' : abs (t m - t n) < ε / (2 * Ns), from HTε _ _ (le.trans !le_max_right Hm) (le.trans !le_max_right Hn),
    have HSε' : abs (s m - s n) < ε / (2 * Nt), from HSε _ _ (le.trans !le_max_left Hm) (le.trans !le_max_left Hn),
    have Habs1 : abs (s m) * abs (t m - t n) < ε / 2, from calc
      abs (s m) * abs (t m - t n) ≤ Ns * abs (t m - t n) : algebra.mul_le_mul_of_nonneg_right !HNs !abs_nonneg
      ... < Ns * (ε / ((2 : ℚ) * Ns)) : algebra.mul_lt_mul_of_pos_left HTε' Nsge0
      ... = ε / 2 : sorry, -- simp
    have Habs2 : abs (s m - s n) * abs (t n) < ε / 2, from calc
      abs (s m - s n) * abs (t n) ≤  abs (s m - s n) * Nt : algebra.mul_le_mul_of_nonneg_left !HNt !abs_nonneg
      ... < (ε / ((2 : ℚ) * Nt)) * Nt : algebra.mul_lt_mul_of_pos_right HSε' Ntge0
      ... = ε / 2 : sorry, -- simp
    apply (calc
      abs (s m * (t m - t n) + (s m - s n) * t n) ≤ abs (s m * (t m - t n)) + abs ((s m - s n) * t n) : abs_add_le_abs_add_abs
      ... = abs (s m) * abs (t m - t n) + abs (s m - s n) * abs (t n) : by rewrite 2 abs_mul
      ... < ε / 2 + ε / 2 : add_lt_add_of_lt_of_lt Habs1 Habs2
      ... = ε : add_halves_helper)
  end

-- splitting into lemmas makes it around 4 sec
theorem mul_cauchy_of_cauchy (s t : cauchy_sequence) : cauchy (s * t) :=
  begin
    have Hs : cauchy s, from cauchy_sequence.is_cauchy s,
    have Ht : cauchy t, from cauchy_sequence.is_cauchy t,
    rewrite [↑cauchy at *, ↑mul],
    apply exists.elim, exact (bounded_of_cauchy Hs),
    intros [Ns, HNs],
    apply exists.elim, exact (bounded_of_cauchy Ht),
    intros [Nt, HNt, ε, Hε],
    have Ns0 : (0 : ℚ) ≤ Ns, from algebra.le.trans (algebra.abs_nonneg (s 0)) (HNs 0),
    have Nt0 : (0 : ℚ) ≤ Nt, from algebra.le.trans (algebra.abs_nonneg (t 0)) (HNt 0),
    have Nsor : Ns = (0 : ℚ) ∨ 0 < Ns, from algebra.eq_or_lt_of_not_lt (algebra.not_lt_of_le Ns0),
    have Ntor : Nt = (0 : ℚ) ∨ 0 < Nt, from algebra.eq_or_lt_of_not_lt (algebra.not_lt_of_le Nt0),
    apply (or.elim Nsor),
    {intro Nseq0, exact (mul_cauchy_helper_1 s t ε Ns HNs Hε Nseq0)},
    intro Nsge0,
    apply (or.elim Ntor),
    {intro Nteq0, exact (mul_cauchy_helper_2 s t ε Nt HNt Hε Nteq0)},
    {intro Ntge0, exact (mul_cauchy_helper_3 s t Hs Ht ε Ns Nt HNs HNt Hε Nsge0 Ntge0)}
  end

-- 4.3 sec
/-theorem mul_cauchy_of_cauchy (s t : cauchy_sequence) : cauchy (s * t) :=
  begin
    have Hs : cauchy s, from cauchy_sequence.is_cauchy s,
    have Ht : cauchy t, from cauchy_sequence.is_cauchy t,
    rewrite [↑cauchy at *, ↑mul],
    apply exists.elim, exact (bounded_of_cauchy Hs),
    intros [Ns, HNs],
    apply exists.elim, exact (bounded_of_cauchy Ht),
    intros [Nt, HNt, ε, Hε],
    have Ns0 : (0 : ℚ) ≤ Ns, from algebra.le.trans (algebra.abs_nonneg (s 0)) (HNs 0),
    have Nt0 : (0 : ℚ) ≤ Nt, from algebra.le.trans (algebra.abs_nonneg (t 0)) (HNt 0),
    have Nsor : Ns = (0 : ℚ) ∨ 0 < Ns, from algebra.eq_or_lt_of_not_lt (algebra.not_lt_of_le Ns0),
    have Ntor : Nt = (0 : ℚ) ∨ 0 < Nt, from algebra.eq_or_lt_of_not_lt (algebra.not_lt_of_le Nt0),
    apply (or.elim Nsor),
    {intro Nseq0,
    fapply exists.intro, exact 0, intros [m, n, Hm, Hn],
    have H0 : ∀ k, abs (s k) = 0, from (take k, abs_eq_zero_of_abs_le_zero (Nseq0 ▸ (HNs k))),
    apply (calc
      abs (s m * t m - s n * t n) ≤ abs (s m * t m) + abs (-(s n * t n)) : abs_add_le_abs_add_abs
      ... = abs (s m) * abs (t m) + abs (s n) * abs (t n) : by rewrite [abs_neg, 2 abs_mul]
      ... = 0 : by rewrite [2 H0, 2 algebra.zero_mul, algebra.zero_add]
      ... < ε : Hε)},
    intro Nsge0,
    apply (or.elim Ntor),
    {intro Nteq0,
    fapply exists.intro, exact 0, intros [m, n, Hm, Hn],
    have H0 : ∀ k, abs (t k) = 0, from (take k, abs_eq_zero_of_abs_le_zero (Nteq0 ▸ (HNt k))),
    apply (calc
      abs (s m * t m - s n * t n) ≤ abs (s m * t m) + abs (-(s n * t n)) : abs_add_le_abs_add_abs
      ... = abs (s m) * abs (t m) + abs (s n) * abs (t n) : by rewrite [abs_neg, 2 abs_mul]
      ... = 0 : by rewrite [2 H0, 2 algebra.mul_zero, algebra.zero_add]
      ... < ε : Hε)},
    {intro Ntge0,
    apply exists.elim, exact (Hs (ε / ((2 : ℚ) * Nt)) (pos_div_helper Hε Ntge0)), intros [Sε, HSε],
    apply exists.elim, exact (Ht (ε / ((2 : ℚ) * Ns)) (pos_div_helper Hε Nsge0)), intros [Tε, HTε],
    fapply exists.intro,
    exact (max Sε Tε),
    intros [m, n, Hm, Hn],
    rewrite [-algebra.add_zero (s m * t m), -algebra.sub_self (s m * t n), algebra.add.comm (s m * t n),
      -algebra.add.assoc, algebra.add.assoc, -algebra.mul_sub_left_distrib,
      -algebra.mul_sub_right_distrib],
    have HTε' : abs (t m - t n) < ε / (2 * Ns), from HTε _ _ (le.trans !le_max_right Hm) (le.trans !le_max_right Hn),
    have HSε' : abs (s m - s n) < ε / (2 * Nt), from HSε _ _ (le.trans !le_max_left Hm) (le.trans !le_max_left Hn),
    have Habs1 : abs (s m) * abs (t m - t n) < ε / 2, from calc
      abs (s m) * abs (t m - t n) ≤ Ns * abs (t m - t n) : algebra.mul_le_mul_of_nonneg_right !HNs !abs_nonneg
      ... < Ns * (ε / ((2 : ℚ) * Ns)) : algebra.mul_lt_mul_of_pos_left HTε' Nsge0
      ... = ε / 2 : sorry, -- simp
    have Habs2 : abs (s m - s n) * abs (t n) < ε / 2, from calc
      abs (s m - s n) * abs (t n) ≤  abs (s m - s n) * Nt : algebra.mul_le_mul_of_nonneg_left !HNt !abs_nonneg
      ... < (ε / ((2 : ℚ) * Nt)) * Nt : algebra.mul_lt_mul_of_pos_right HSε' Ntge0
      ... = ε / 2 : sorry, -- simp
    apply (calc
      abs (s m * (t m - t n) + (s m - s n) * t n) ≤ abs (s m * (t m - t n)) + abs ((s m - s n) * t n) : abs_add_le_abs_add_abs
      ... = abs (s m) * abs (t m - t n) + abs (s m - s n) * abs (t n) : by rewrite 2 abs_mul
      ... < ε / 2 + ε / 2 : add_lt_add_of_lt_of_lt Habs1 Habs2
      ... = ε : add_halves_helper)}
  end-/


-- show setoid cauchy_sequence

definition zero_seq : rat_sequence := λ n, 0
theorem zero_is_cauchy : cauchy zero_seq :=
  begin
    rewrite [↑zero_seq, ↑cauchy],
    intros [ε, Hε],
    fapply exists.intro,
    exact 0,
    intros [m, n, Hm, Hn],
    rewrite [algebra.sub_zero, abs_zero],
    exact Hε
  end

definition one_seq : rat_sequence := λ n, 1
theorem one_is_cauchy : cauchy one_seq :=
  begin
    rewrite [↑one_seq, ↑cauchy],
    intros [ε, Hε],
    fapply exists.intro,
    exact 0,
    intros [m, n, Hm, Hn],
    rewrite [algebra.sub_self, abs_zero],
    exact Hε
  end

-- this isn't true, is it?
theorem vanishes_is_decidable [instance] (s : rat_sequence) : decidable (vanishes s) :=
  sorry

definition cauchy.add (s t : cauchy_sequence) : cauchy_sequence :=
  cauchy_sequence.mk (s + t) (add_cauchy_of_cauchy _ _) -- why doesn't this work with ! ?

definition cauchy.neg (s : cauchy_sequence) : cauchy_sequence :=
  cauchy_sequence.mk (-s) (neg_cauchy_of_cauchy _)

definition cauchy.sub (s t : cauchy_sequence) : cauchy_sequence :=
  cauchy_sequence.mk (s - t) (sub_cauchy_of_cauchy _ _)

definition cauchy.mul (s t : cauchy_sequence) : cauchy_sequence :=
  cauchy_sequence.mk (s * t) (mul_cauchy_of_cauchy _ _)

definition cauchy.inv (s : cauchy_sequence) : cauchy_sequence :=
  decidable.cases_on (vanishes_is_decidable s)
    (take H, cauchy_sequence.mk zero_seq zero_is_cauchy)
    (take H, cauchy_sequence.mk (s⁻¹) (inv_cauchy_of_nonzero_cauchy _ H))

infix `+` := cauchy.add
prefix `-` := cauchy.neg
infix `-` := cauchy.sub
infix `*` := cauchy.mul
postfix `⁻¹` := cauchy.inv

definition cauchy.equiv [reducible] (s t : cauchy_sequence) : Prop :=
  seq.equiv s t
notation p `≡` q := cauchy.equiv p q

--check fun s t : cauchy_sequence, seq.equiv s t

theorem cauchy.equiv.refl (s : cauchy_sequence) : s ≡ s :=
  seq.equiv.refl s

theorem cauchy.equiv.symm (s t : cauchy_sequence) (H : s ≡ t) : t ≡ s :=
  seq.equiv.symm H

theorem cauchy.equiv.trans (r s t : cauchy_sequence) (H1 : r ≡ s) (H2 : s ≡ t) : r ≡ t :=
  seq.equiv.trans H1 H2

theorem cauchy.equiv.is_equiv : equivalence cauchy.equiv :=
  mk_equivalence cauchy.equiv cauchy.equiv.refl cauchy.equiv.symm cauchy.equiv.trans

definition cauchy.to_setoid [instance] : setoid cauchy_sequence :=
  ⦃setoid, r := cauchy.equiv, iseqv := cauchy.equiv.is_equiv ⦄

end cauchy

/-definition real := quot cauchy.to_setoid

constants q r s : cauchy_sequence
check q * s-/

theorem seq_dist_sub (q r s t : cauchy_sequence) : cauchy.sub (cauchy.add q r) (cauchy.add s t) = q + r - s - t := sorry

theorem seq_comm (q r s t : cauchy_sequence) : q + r - s - t = (q - s) + (r - t) := sorry

theorem blah (q r s t : cauchy_sequence) (H1 : vanishes (q - s)) (H2 : vanishes (r - t)) : vanishes (cauchy.sub (cauchy.add (q)  (r))  (cauchy.add (s)  (t))) := sorry

theorem add.well_defined (q r s t : cauchy_sequence) (H1 : q ≡ s) (H2 : r ≡ t) :
   q + r ≡ s + t :=
  /- begin
     rewrite [↑cauchy.equiv at *, ↑seq.equiv at *],
     apply blah,
   end-/ sorry

theorem neg.well_defined (q r : cauchy_sequence) (H1 : q ≡ r) : -q ≡ -r := sorry

theorem sub.well_defined (q r s t : cauchy_sequence) (H1 : q ≡ s) (H2 : r ≡ t) :
  q - r ≡ s - t := sorry

theorem mul.well_defined (q r s t : cauchy_sequence) (H1 : q ≡ s) (H2 : r ≡ t) :
   q * r ≡ s * t := sorry

theorem inv.well_defined (q r : cauchy_sequence) (H1 : q ≡ r) : q⁻¹ ≡ r⁻¹ := sorry

end sequence
