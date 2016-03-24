/-
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Basic properties of matrices and vectors. Proof of Motzkin's transposition theorem.
-/

import data.real data.fin algebra.module
open nat rat

namespace matrix

definition matrix [reducible] (A : Type) (m n : ℕ) := fin m → fin n → A

notation `M_(`m`, `n`)` := matrix _ m n
notation `M[`A`]_(`m`, `n`)` := matrix A m n

-- should rvector and cvector just be notation?

definition rvector [reducible] (A : Type) (n : ℕ) := M[A]_(1, n)

definition cvector [reducible] (A : Type) (m : ℕ) := M[A]_(m, 1)

definition mval {A : Type} (M : matrix A 1 1) : A :=
  M !fin.zero !fin.zero

-- useful for testing
definition cvector_of_list {A : Type} (l : list A) : cvector A (list.length l) :=
  λ i j, list.ith l (fin.val i) !fin.val_lt

definition rvector_of_list {A : Type} (l : list A) : rvector A (list.length l) :=
  λ i j, list.ith l (fin.val j) !fin.val_lt

section matrix_defs

variable {A : Type}
variables {m n k : ℕ}

definition col_of (M : matrix A m n) (j : fin n) : cvector A m := λ a b, M a j

definition row_of (M : matrix A m n) (i : fin m) : rvector A n := λ a b, M i b

definition r_ith (v : rvector A n) (i : fin n) := v !fin.zero i

definition c_ith (v : cvector A m) (i : fin m) := v i !fin.zero

definition nonneg [reducible] [weak_order A] [has_zero A] (M : matrix A m n) := ∀ i j, M i j ≥ 0

definition le [reducible] [has_le A] (M N : matrix A m n) := ∀ i j, M i j ≤ N i j

definition lt [reducible] [has_lt A] (M N : matrix A m n) := ∀ i j, M i j < N i j

definition r_dot [semiring A] (u v : rvector A n) := Suml (fin.upto n) (λ i, r_ith u i * r_ith v i)

definition c_dot [semiring A] (u v : cvector A m) := Suml (fin.upto m) (λ i, c_ith u i * c_ith v i)

definition transpose (M : matrix A m n) : matrix A n m := λ a b, M b a
notation M`^Tr` := transpose M

definition dot [semiring A] (u : rvector A n) (v : cvector A n) := c_dot (u^Tr) v

theorem transpose_transpose (M : matrix A m n) : (M^Tr)^Tr = M := rfl

theorem c_ith_cvector_of_rvector_eq_c_ith (u : rvector A n) (i : fin n) :
        c_ith (transpose u) i = r_ith u i :=
  rfl

theorem r_dot_zero [semiring A] (u : rvector A n) : r_dot u (λ a b, 0) = 0 :=
  begin
    unfold r_dot,
    have H : (λ i, r_ith u i * r_ith (λ (a : fin 1) (b : fin n), 0) i) = (λ i, 0), begin
      apply funext, intro,
      rewrite [↑r_ith, mul_zero]
    end,
    rewrite H,
    apply Suml_zero
  end

theorem r_zero_dot [semiring A] (u : rvector A n) : r_dot (λ a b, 0) u = 0 :=
  begin
    unfold r_dot,
    have H : (λ i, r_ith (λ (a : fin 1) (b : fin n), 0) i * r_ith u i) = (λ i, 0), begin
      apply funext, intro,
      rewrite [↑r_ith, zero_mul]
    end,
    rewrite H,
    apply Suml_zero
  end

theorem c_dot_zero [semiring A] (u : cvector A n) : c_dot u (λ a b, 0) = 0 :=
  begin
    unfold c_dot,
    have H : (λ i, c_ith u i * c_ith (λ (a : fin n) (b : fin 1), 0) i) = (λ i, 0), begin
      apply funext, intro,
      rewrite [↑c_ith, mul_zero]
    end,
    rewrite H,
    apply Suml_zero
  end

theorem c_zero_dot [semiring A] (u : cvector A n) : c_dot (λ a b, 0) u = 0 :=
  begin
    unfold c_dot,
    have H : (λ i, c_ith (λ (a : fin n) (b : fin 1), 0) i * c_ith u i) = (λ i, 0), begin
      apply funext, intro,
      rewrite [↑c_ith, zero_mul]
    end,
    rewrite H,
    apply Suml_zero
  end

theorem dot_zero [semiring A] (u : rvector A n) : dot u (λ a b, 0) = 0 :=
  !c_dot_zero

theorem zero_dot [semiring A] (u : cvector A n) : dot (λ a b, 0) u = 0 :=
  !c_zero_dot

definition mul [semiring A] (M : matrix A m n) (N : matrix A n k) : matrix A m k :=
  λ (a : fin m) (b : fin k), c_dot (transpose (row_of M a)) (col_of N b)

infix `⬝` := mul

theorem dot_eq_mul [semiring A] (u : rvector A n) (v : cvector A n) : dot u v = (u ⬝ v) !fin.zero !fin.zero :=
  rfl

theorem row_of_rvector (v : rvector A n) : row_of v !fin.zero = v :=
  funext (λ x, by rewrite (fin.fin_one_eq_zero x))

theorem col_of_cvector (v : cvector A m) : col_of v !fin.zero = v :=
  begin
    apply funext,
    intro x,
    apply funext,
    intro y,
    unfold col_of,
    rewrite (fin.fin_one_eq_zero y)
  end

theorem row_of_ith (M : matrix A m n) (x : fin m) (y : fin n) : (row_of M x) !fin.zero y = M x y :=
  rfl

theorem col_of_ith (M : matrix A m n) (x : fin m) (y : fin n) : (col_of M y) x !fin.zero = M x y :=
  rfl

/- Suml theorems. These need a better home, but I'm not sure where. -/

variables {B C T : Type} (l : list T)

theorem Suml_assoc [semiring A] (la : list B) (lb : list C) (f : B → C → A) :
        Suml la (λ a, Suml lb (λ b, f a b))
          = Suml lb (λ b, Suml la (λ a, f a b)) :=
  begin
    induction la with h tt ih,
    {induction lb with h' tt' ih',
    {rewrite Suml_nil},
    {rewrite [Suml_nil at *, Suml_cons, -ih', add_zero]}},
    {induction lb with h' tt' ih',
    {rewrite [Suml_cons, *Suml_nil at *, ih, add_zero]},
    {rewrite [Suml_cons, ih, -Suml_add],
    congruence,
    apply funext,
    intro b,
    rewrite Suml_cons}}
  end

theorem mul_Suml [semiring A] (a : A) (f : T → A) :
        a * Suml l f = Suml l (λ k, a * f k) :=
  begin
    induction l with h tt ih,
    rewrite [Suml_nil, mul_zero],
    rewrite [*Suml_cons, left_distrib, ih]
  end

theorem Suml_mul [semiring A] (a : A) (f : T → A) :
         (Suml l f) * a = Suml l (λ k, f k * a) :=
  begin
    induction l with h tt ih,
    rewrite [Suml_nil, zero_mul],
    rewrite [*Suml_cons, right_distrib, ih]
  end

theorem Suml_nonneg_of_nonneg [ordered_semiring A] (f : T → A)
        (H : Π (i : ℕ) (Hi : i < list.length l), f (list.ith l i Hi) ≥ 0) : Suml l f ≥ (0 : A) :=
  begin
    induction l with h tt ih,
    rewrite Suml_nil,
    apply le.refl,
    rewrite Suml_cons,
    have Hh : f h ≥ 0, begin
      note Hl := H 0 !list.length_cons_pos,
      rewrite list.ith_zero at Hl,
      apply Hl
    end,
    have Htt : Suml tt f ≥ 0, begin
      apply ih,
      intro i Hi,
      have Hsucc : succ i < list.length (list.cons h tt),
        by rewrite list.length_cons; apply nat.add_lt_add_right Hi,
      note Ho := H (succ i) Hsucc,
      rewrite list.ith_succ at Ho,
      apply Ho
    end,
    exact add_nonneg Hh Htt
  end

theorem Suml_le_of_le [ordered_semiring A] (f g : T → A) (H : ∀ t : T, f t ≤ g t) :
        Suml l f ≤ Suml l g :=
  begin
    induction l,
    {rewrite *Suml_nil, apply le.refl},
    {rewrite *Suml_cons, apply add_le_add, apply H, assumption}
  end

theorem Suml_lt_of_lt [ordered_semiring A] (Hl : l ≠ list.nil) (f g : T → A)
        (H : ∀ t : T, f t < g t) : Suml l f < Suml l g :=
  begin
    induction l,
    {apply absurd !rfl Hl},
    {rewrite [*Suml_cons],
    apply add_lt_add_of_lt_of_le,
    apply H,
    induction a_1,
    rewrite *Suml_nil,
    apply le.refl,
    apply le_of_lt,
    apply v_0_1,
    contradiction}
  end

theorem eq_of_Suml_eq_Suml_of_le [ordered_ring A] (f g : T → A) (H : ∀ t : T, f t ≤ g t)
       (HSeq : Suml l f = Suml l g) : ∀ t : T, list.mem t l → f t = g t :=
  begin
    induction l,
    intros,
    contradiction,
    intro t Ht,
    rewrite 2 Suml_cons at HSeq,
    have H1 : Suml a_1 f ≥ Suml a_1 g, from calc
      Suml a_1 f = -f a + (f a + Suml a_1 f) : by rewrite neg_add_cancel_left
             ... = (-f a + g a) + Suml a_1 g : by rewrite [HSeq, -add.assoc]
             ... ≥ Suml a_1 g : begin apply le_add_of_nonneg_left, rewrite add.comm, apply sub_nonneg_of_le !H end,
    have H2 : Suml a_1 f ≤ Suml a_1 g, by apply Suml_le_of_le; exact H,
    cases (list.eq_or_mem_of_mem_cons Ht) with Eta Mta,
    note Heq := eq_of_le_of_ge H2 H1,
    rewrite [Heq at HSeq, Eta],
    apply eq_of_add_eq_add_right HSeq,
    apply v_0,
    exact eq_of_le_of_ge H2 H1,
    exact Mta
  end

theorem Suml_le_of_le_strong [ordered_semiring A] (f g : T → A)
        (H : ∀ t : T, list.mem t l → f t ≤ g t) : Suml l f ≤ Suml l g :=
  begin
    induction l,
    {rewrite *Suml_nil, apply le.refl},
    {rewrite *Suml_cons,
    apply add_le_add,
    apply H,
    apply list.mem_cons,
    apply v_0, intros,
    apply H,
    apply list.mem_cons_of_mem,
    assumption}
  end

theorem Suml_mul_Suml_eq_Suml_Suml_mul [semiring A] (l1 : list B) (l2 : list C) (f : B → A) (g : B → C → A) :
        Suml l1 (λ s, f s * Suml l2 (λ t, g s t)) = Suml l1 (λ s, Suml l2 (λ t, f s * g s t)) :=
  begin
    congruence,
    apply funext,
    intro s,
    rewrite mul_Suml
  end

/- ------------------------- -/

theorem m_mul_assoc [semiring A] {o p : ℕ} (M : matrix A m n) (N : matrix A n o) (O : matrix A o p) :
        M ⬝ (N ⬝ O) = (M ⬝ N) ⬝ O :=
  begin
    rewrite ↑mul,
    repeat (apply funext; intro),
    rewrite [↑c_dot, ↑c_ith, ↑row_of, ↑transpose, ↑col_of, Suml_mul_Suml_eq_Suml_Suml_mul, Suml_assoc],
    congruence, apply funext, intro,
    rewrite Suml_mul,
    congruence, apply funext, intro,
    rewrite mul.assoc
  end

/- order, sign theorems -/

theorem transpose_nonneg_of_nonneg [weak_order A] [has_zero A] {u : rvector A n} (Hu : nonneg u) :
        nonneg (transpose u) :=
  λ i j, !Hu

theorem c_dot_nonneg_of_nonneg [ordered_semiring A] (u v : cvector A m) (Hu : nonneg u) (Hv : nonneg v) :
        c_dot u v ≥ 0 :=
  begin
    unfold c_dot,
    apply Suml_nonneg_of_nonneg,
    intros,
    apply mul_nonneg,
    apply Hu,
    apply Hv
  end

theorem dot_nonneg_of_nonneg [ordered_semiring A] (u v : cvector A m) (Hu : nonneg u) (Hv : nonneg v) :
        c_dot u v ≥ 0 :=
  c_dot_nonneg_of_nonneg _ _ Hu Hv

theorem row_of_nonneg_of_nonneg [weak_order A] [has_zero A] {M : matrix A m n} (HM : nonneg M) (i : fin m) :
        nonneg (row_of M i) :=
  λ a b, !HM

theorem col_of_nonneg_of_nonneg [weak_order A] [has_zero A] {M : matrix A m n} (HM : nonneg M) (i : fin n) :
        nonneg (col_of M i) :=
  λ a b, !HM

theorem mul_nonneg_of_nonneg [ordered_semiring A] (M : matrix A m n) (N : matrix A n k)
        (HM : nonneg M) (HN : nonneg N) : nonneg (M ⬝ N) :=
  begin
    intros,
    unfold mul,
    apply c_dot_nonneg_of_nonneg,
    apply transpose_nonneg_of_nonneg,
    apply row_of_nonneg_of_nonneg HM,
    apply col_of_nonneg_of_nonneg HN
  end

theorem dot_le_dot_of_nonneg_of_le [ordered_semiring A] (u : rvector A n) (v1 v2 : cvector A n)
        (Hu : nonneg u) (Hv : ∀ i, c_ith v1 i ≤ c_ith v2 i) : dot u v1 ≤ dot u v2 :=
  begin
    unfold [dot, c_dot, transpose],
    apply Suml_le_of_le,
    intro,
    apply mul_le_mul_of_nonneg_left,
    apply Hv,
    apply Hu
  end

theorem dot_lt_dot_of_nonneg_of_nonzero_of_lt [linear_ordered_ring A]
        (u : rvector A n) (v1 v2 : cvector A n) (Hu : nonneg u) (i : fin n)
        (Hunz : r_ith u i > 0) (Hv : ∀ i, c_ith v1 i < c_ith v2 i) : dot u v1 < dot u v2 :=
  begin
    apply lt_of_not_ge,
    intro Hge,
    have Hle : dot u v1 ≤ dot u v2, begin
      apply dot_le_dot_of_nonneg_of_le,
      apply Hu,
      intro, apply le_of_lt, apply Hv
    end,
    note Heq := eq_of_le_of_ge Hle Hge,
    have Hilt : r_ith u i * c_ith v1 i < r_ith u i * c_ith v2 i, begin
      apply mul_lt_mul_of_pos_left,
      apply Hv,
      apply Hunz
    end,
    have Hmsle : ∀ t, r_ith u t * c_ith v1 t ≤ r_ith u t * c_ith v2 t, begin
      intro,
      apply mul_le_mul_of_nonneg_left,
      apply le_of_lt !Hv,
      apply Hu
    end,
    note Hmeq := eq_of_Suml_eq_Suml_of_le _ _ _ Hmsle Heq i !fin.mem_upto,
    rewrite Hmeq at Hilt,
    exact !not_lt_self Hilt
  end

end matrix_defs

section inst_dec

/- instances -/

variables (A : Type) (m n : ℕ)

theorem matrix_inhabited [instance] [HA : inhabited A] :
        inhabited (M[A]_(succ m, succ n)) :=
  inhabited.rec_on HA (λ a, inhabited.mk (λ s t, a))

open list
definition decidable_quant [instance] (P : fin n → Prop) [∀ k, decidable (P k)] : decidable (∀ k, P k) :=
  if H : all (fin.upto n) P then
    decidable.inl (λ k, of_mem_of_all !fin.mem_upto H)
  else
    decidable.inr (λ Hpk, H (all_of_forall (λ a Ha, Hpk a)))

definition matrix_decidable_eq [instance] [decidable_eq A] : decidable_eq (matrix A m n) :=
  λ M N : matrix A m n,
  if H : ∀ i : fin m, ∀ j : fin n, M i j = N i j then
    decidable.inl (funext (λ i, funext (λ j, H i j)))
  else
    decidable.inr (begin intro Heq, apply H, intros, congruence, exact Heq end)

/- matrix A m n is not a strict order if either m or n is 0. If it would be useful,
   we could prove
    order_pair (matrix A (succ m) n)
   and
    order_pair (matrix A m (succ n)).
-/
definition is_weak_order [instance] [order_pair A] : weak_order (matrix A m n) :=
  begin
    fapply weak_order.mk,
    {exact le},
    {unfold le, intros, apply le.refl},
    {unfold le, intros, apply le.trans !a_1 !a_2},
    {unfold le, intros, repeat (apply funext; intro), apply eq_of_le_of_ge !a_1 !a_2}
  end

end inst_dec

section matrix_arith_m_n

definition m_add {A : Type} [has_add A] {m n : ℕ} (B C : matrix A m n) : matrix A m n :=
  λ x y, B x y + C x y

definition m_neg {A : Type} [has_neg A] {m n : ℕ} (B : matrix  A m n) : matrix A m n :=
  λ x y, -B x y

definition m_smul {A : Type} [has_mul A] {m n : ℕ} (c : A) (B : matrix A m n) : matrix A m n :=
  λ x y, c * B x y

definition m_left_module [instance] [reducible] (A : Type) [ring A] (m n : ℕ) : left_module A (matrix A m n) :=
  begin
    fapply left_module.mk,
    {exact m_smul},
    {exact m_add},
    {intros, unfold m_add, repeat (apply funext; intro), rewrite add.assoc},
    {exact λ a b, 0},
    {intros, unfold m_add, repeat (apply funext; intro), rewrite zero_add},
    {intros, unfold m_add, repeat (apply funext; intro), rewrite add_zero},
    {exact m_neg},
    {intros, rewrite [↑m_neg, ↑m_add], repeat (apply funext; intro), rewrite add.left_inv},
    {intros, unfold m_add, repeat (apply funext; intro), rewrite add.comm},
    {intros, rewrite [↑m_smul, ↑m_add], repeat (apply funext; intro), rewrite left_distrib},
    {intros, rewrite [↑m_smul, ↑m_add], repeat (apply funext; intro), rewrite -right_distrib},
    {intros, unfold m_smul, repeat (apply funext; intro), rewrite mul.assoc},
    {intro, unfold m_smul, repeat (apply funext; intro), rewrite one_mul}
  end

variables {A : Type}

theorem Suml_neg [add_comm_group A] {T : Type} (l : list T) (f : T → A) : -(Suml l f) = Suml l (λ t, - f t) :=
  begin
    apply neg_eq_of_add_eq_zero,
    have H : (λ x, f x + -f x) = (λ x, 0), from funext (λ x, !sub_self),
    rewrite [-Suml_add, H],
    apply Suml_zero
  end

theorem distrib_dot_right [ring A] (n : ℕ) (M N : rvector A n) (x : cvector A n) :
        dot (M + N) x = dot M x + dot N x :=
  begin
    change dot (m_add M N) x = (dot M x) + (dot N x),
    rewrite [↑dot, ↑c_dot, ↑m_add, ↑transpose, ↑c_ith, -Suml_add],
    congruence,
    apply funext, intro,
    rewrite right_distrib
  end

theorem distrib_smul_right [ring A] (m n o : ℕ) (M N : matrix A m n) (x : matrix A n o) :
        (M + N) ⬝ x = M ⬝ x + N ⬝ x :=
  begin
    change (m_add M N) ⬝ x = m_add (M ⬝ x) (N ⬝ x),
    rewrite [↑mul, ↑c_dot, ↑m_add],
    repeat (apply funext; intro),
    rewrite [↑c_ith, ↑row_of, ↑col_of, ↑transpose, -Suml_add],
    congruence,
    apply funext, intro,
    rewrite right_distrib
  end

theorem neg_matrix [ring A] (m n : ℕ) (M : matrix A m n) : -M = (λ a b, -M a b) := rfl

theorem zero_matrix [ring A] (m n : ℕ) : (0 : matrix A m n) = (λ a b, 0) := rfl


theorem matrix_add_app [ring A] (m n : ℕ) (M N : matrix A m n) (a : fin m) (b : fin n) :
        (M + N) a b = M a b + N a b := rfl

theorem neg_smul [ring A] (m n o : ℕ) (M : matrix A m n) (N : matrix A n o) : (-M) ⬝ N = - (M ⬝ N) :=
  begin
    rewrite [↑mul],
    repeat (apply funext; intro),
    unfold [c_dot, row_of, col_of, c_ith, transpose],
    rewrite [2 neg_matrix, Suml_neg],
    congruence,
    apply funext, intro,
    rewrite neg_mul_eq_neg_mul
  end

theorem zero_smul [ring A] (l m n : ℕ) (M : matrix A m n) : (0 : matrix A l m) ⬝ M = 0 :=
  begin
    rewrite [↑mul, 2 zero_matrix],
    repeat (apply funext; intro),
    unfold [c_dot, row_of, col_of, transpose, c_ith],
    have H : (λ i, 0 * M i x_1) = (λ i, 0), from funext (λ i, !zero_mul),
    rewrite H,
    apply Suml_zero
  end

theorem smul_zero [ring A] (l m n : ℕ) (M : matrix A l m) : M ⬝ (0 : matrix A m n) = 0 :=
  begin
    rewrite [↑mul, 2 zero_matrix],
    repeat (apply funext; intro),
    unfold [c_dot, row_of, col_of, transpose, c_ith],
    have H : (λ i, M x i * 0) = (λ i, 0), from funext (λ i, !mul_zero),
    rewrite H,
    apply Suml_zero
  end

theorem le_iff_forall_row [weak_order A] {n : ℕ} (u v : rvector A n) :
        u ≤ v ↔ ∀ i, r_ith u i ≤ r_ith v i :=
  begin
    replace u ≤ v with le u v,
    unfold le,
    apply iff.intro,
    {intros H i, apply H},
    {intros H i j, rewrite fin.fin_one_eq_zero, apply H}
  end

theorem le_iff_forall_col [weak_order A] {n : ℕ} (u v : cvector A n) :
        u ≤ v ↔ ∀ i, c_ith u i ≤ c_ith v i :=
  begin
    replace u ≤ v with le u v,
    unfold le,
    apply iff.intro,
    {intros H i, apply H},
    {intros H i j, rewrite fin.fin_one_eq_zero, apply H}
  end

-- why doesn't rfl work to prove this?
theorem nonneg_iff_le_zero_row [ordered_ring A] {n : ℕ} (u : rvector A n) :
        nonneg u ↔ (0 : rvector A n) ≤ u :=
  begin
    change nonneg u ↔ le (λ a b, 0) u,
    reflexivity
  end

theorem nonneg_iff_le_zero_col [ordered_ring A] {n : ℕ} (u : cvector A n) :
        nonneg u ↔ (0 : cvector A n) ≤ u :=
  begin
    change nonneg u ↔ le (0 : cvector A n) u,
    reflexivity
  end

end matrix_arith_m_n

section motzkin_transposition
variables {A : Type} [linear_ordered_ring A]

/-
  n variables
  a strict ineqs  P : M[A]_(a, n), p : cvector a
  b weak ineqs  Q : M[A]_(b, n), q : cvector b
  c eqs  R : M[A]_(c, n), r : cvector c

  There are various ways to express Hsum equivalently: eg,
    (y ⬝ P) + (z ⬝ Q) + (t ⬝ R) = (0 : rvector A n).
-/
variables {a b c n : ℕ}
        (P : M[A]_(a, n)) (Q : M[A]_(b, n)) (R : M[A]_(c, n))
        (p : cvector A a) (q : cvector A b) (r : cvector A c)
        (y : rvector A a) (z : rvector A b) (t : rvector A c)
        (Hnny : nonneg y) (Hnnz : nonneg z)
        (Hsum : ∀ i : fin n, r_ith (y ⬝ P) i + r_ith (z ⬝ Q) i + r_ith (t ⬝ R) i = 0)

include Hsum

-- .3 seconds to elaborate
private theorem dot_eq_zero {x : cvector A n} (HsatR : ∀ i : fin c, c_ith (R⬝x) i = c_ith r i) :
        dot y (P ⬝ x) + dot z (Q ⬝ x) + dot t r = 0 :=
  begin
    have Hneg : (y ⬝ P) + (z ⬝ Q) + (t ⬝ R) = (0 : rvector A n), begin
      change (λ a b, (y⬝P + z⬝Q + t⬝R) a b) = (λ a b, 0),
      repeat (apply funext; intro),
      rewrite fin.fin_one_eq_zero,
      apply Hsum
    end,
    have Hr : R⬝x = r, begin
      repeat (apply funext; intro),
      rewrite fin.fin_one_eq_zero,
      apply HsatR
    end,
    have Hneg' : ((y ⬝ P) + (z ⬝ Q) + (t ⬝ R)) ⬝ x = 0 ⬝ x, by rewrite Hneg, -- this line and the following take about .1 sec
    rewrite [2 distrib_smul_right at Hneg',  -3 m_mul_assoc at Hneg', Hr at Hneg',
            zero_smul at Hneg', zero_matrix at Hneg'],
    have Hneg'' : (λ a b : fin 1, (y⬝(P⬝x) + z⬝(Q⬝x) + t⬝r) a b) = (λ a b : fin 1, 0), from Hneg',
    have Heqz : (y⬝(P⬝x) + z⬝(Q⬝x) + t⬝r) !fin.zero !fin.zero = 0, by rewrite Hneg'',
    have Heqz' : (y⬝(P⬝x)) !fin.zero !fin.zero + (z⬝(Q⬝x)) !fin.zero !fin.zero + (t⬝r) !fin.zero !fin.zero = 0,
               from Heqz,
    rewrite *dot_eq_mul,
    exact Heqz'
  end

include Hnny Hnnz

theorem motzkin_transposition_with_equalities_lt
        (Hlt : (c_dot (y^Tr) p + c_dot (z^Tr) q + c_dot (t^Tr) r < 0)) :
         ¬ ∃ x : cvector A n, (∀ i, c_ith (P ⬝ x) i < c_ith p i) ∧
                              (∀ i, c_ith (Q ⬝ x) i ≤ c_ith q i) ∧
                              (∀ i, c_ith (R ⬝ x) i = c_ith r i) :=
  begin
    intro Hsat,
    cases Hsat with x Hsat,
    cases Hsat with HsatP Hsat,
    cases Hsat with HsatQ HsatR,
    note Heqz' := dot_eq_zero P Q R r y z t Hsum HsatR,
    apply not_lt_self (0 : A),
    rewrite -Heqz' at {1},
    have Hdlt : dot y (P⬝x) + dot z (Q⬝x) + dot t r ≤ dot y p + dot z q + dot t r, begin
      apply add_le_add_right,
      apply add_le_add,
      apply dot_le_dot_of_nonneg_of_le,
      exact Hnny,
      intro i,
      apply le_of_lt,
      apply HsatP,
      apply dot_le_dot_of_nonneg_of_le,
      exact Hnnz,
      exact HsatQ
    end,
    apply lt_of_le_of_lt,
    exact Hdlt,
    exact Hlt
  end

theorem motzkin_transposition_with_equalities_le
        (Hyp : (∃ i, r_ith y i > 0) ∧ c_dot (y^Tr) p + c_dot (z^Tr) q + c_dot (t^Tr) r ≤ 0) :
         ¬ ∃ x : cvector A n, (∀ i, c_ith (P ⬝ x) i < c_ith p i) ∧
                              (∀ i, c_ith (Q ⬝ x) i ≤ c_ith q i) ∧
                              (∀ i, c_ith (R ⬝ x) i = c_ith r i) :=
  begin
    intro Hsat,
    cases Hsat with x Hsat,
    cases Hsat with HsatP Hsat,
    cases Hsat with HsatQ HsatR,
    note Heqz' := dot_eq_zero P Q R r y z t Hsum HsatR,
    apply not_lt_self (0 : A),
    rewrite -Heqz' at {1},
    cases Hyp with Hj Hor2,
    cases Hj with j Hj,
    have Hdlt : dot y (P⬝x) + dot z (Q⬝x) + dot t r < dot y p + dot z q + dot t r, begin
      apply add_lt_add_right,
      apply add_lt_add_of_lt_of_le,
      apply dot_lt_dot_of_nonneg_of_nonzero_of_lt,
      exact Hnny,
      exact Hj,
      exact HsatP,
      apply dot_le_dot_of_nonneg_of_le,
      exact Hnnz,
      exact HsatQ
    end,
    apply lt_of_lt_of_le,
    exact Hdlt,
    exact Hor2
  end

theorem motzkin_transposition_with_equalities
        (Hor : (c_dot (y^Tr) p + c_dot (z^Tr) q + c_dot (t^Tr) r < 0) ∨
               ((∃ i : fin a, r_ith y i > 0) ∧ c_dot (y^Tr) p + c_dot (z^Tr) q + c_dot (t^Tr) r ≤ 0)) :
         ¬ ∃ x : cvector A n, (∀ i : fin a, c_ith (P ⬝ x) i < c_ith p i) ∧
                              (∀ i : fin b, c_ith (Q ⬝ x) i ≤ c_ith q i) ∧
                              (∀ i : fin c, c_ith (R ⬝ x) i = c_ith r i) :=
  begin
    cases Hor with Hor1 Hor2,
    {apply motzkin_transposition_with_equalities_lt,
    exact Hnny, exact Hnnz, exact Hsum, exact Hor1},
    {apply motzkin_transposition_with_equalities_le,
    exact Hnny, exact Hnnz, exact Hsum, exact Hor2}
  end

end motzkin_transposition

section matrix_arith_square
open fin
definition sq_matrix_id (A : Type) [has_zero A] [has_one A] (m : ℕ) : matrix A m m :=
  λ x y, if x = y then 1 else 0

theorem Suml_map {A B C : Type} [add_monoid C] (l : list A) (f : A → B) (g : B → C) :
        Suml (list.map f l) g = Suml l (λ a, g (f a)) :=
  begin
    induction l,
    rewrite Suml_nil,
    rewrite [list.map_cons, *Suml_cons, v_0]
  end

-- this is annoying!
theorem dot_basis_vec {A : Type} [semiring A] {m : ℕ} (k : fin m) (f : fin m → A) :
        Suml (upto m) (λ j, (f j) * if j = k then 1 else 0) = f k :=
  begin
    induction m,
    apply false.elim (false_of_fin_zero k),
    rewrite [upto_succ, Suml_cons],
    cases decidable.em (maxi = k) with Heq Hneq,
    {rewrite [if_pos Heq, -Heq, mul_one, -add_zero (f maxi) at {2}],
    congruence,
    have H : (λ a_1 : fin a, f (lift_succ a_1) * ite (lift_succ a_1 = maxi) 1 0) = (λ a_1, 0), begin
      apply funext,
      intro b,
      rewrite [if_neg lift_succ_ne_max, mul_zero]
    end,
    rewrite [Suml_map, H, Suml_zero]},
    {rewrite [if_neg Hneq, mul_zero, zero_add, Suml_map],
    note Hlt := lt_max_of_ne_max (ne.symm Hneq),
    have Hfk : f k = f (lift_succ (fin.mk (val k) Hlt)), begin
      induction k with kv Hkv,
      exact rfl
    end,
    rewrite [Hfk, -(v_0 (fin.mk (val k) Hlt) (λ v, f (lift_succ v)))],
    congruence, apply funext, intro j,
    cases decidable.em (lift_succ j = k) with Hjk Hnjk,
    have Hjk' : j = mk (val k) Hlt, begin
      induction j with vj Hvj,
      congruence,
      rewrite -Hjk
    end,
    rewrite [if_pos Hjk, if_pos Hjk'],
    have Hjk' : j ≠ mk (val k) Hlt, begin
      intro Hjk,
      apply Hnjk,
      induction k,
      rewrite Hjk
    end,
    rewrite [if_neg Hnjk, if_neg Hjk']}
  end

theorem b_vec_dot' {A : Type} [semiring A] {m : ℕ} (k : fin m) (f : fin m → A) :
        Suml (upto m) (λ j, (if k = j then 1 else 0) * f j) = f k :=
  begin
    have H : (λ j, (if k = j then 1 else 0) * f j) = (λ j, (f j) * if j = k then 1 else 0), begin
      apply funext, intro,
      cases decidable.em (k = x) with Heq Hneq,
      rewrite [if_pos Heq, if_pos (eq.symm Heq), mul_one, one_mul],
      rewrite [if_neg Hneq, if_neg (ne.symm Hneq), mul_zero, zero_mul]
    end,
    rewrite [H, dot_basis_vec]
  end

theorem sq_matrix_mul_one {A : Type} [semiring A] {m : ℕ} (M : matrix A m m) : mul M (sq_matrix_id A m) = M :=
  begin
    rewrite [↑sq_matrix_id, ↑mul],
    repeat (apply funext; intro),
    rewrite [↑row_of, ↑transpose, ↑col_of, ↑c_dot, ↑c_ith, dot_basis_vec]
  end

theorem sq_matrix_one_mul {A : Type} [semiring A] {m : ℕ} (M : matrix A m m) : mul (sq_matrix_id A m) M = M :=
  begin
    rewrite [↑sq_matrix_id, ↑mul],
    repeat (apply funext; intro),
    rewrite [↑row_of, ↑transpose, ↑col_of, ↑c_dot, ↑c_ith, b_vec_dot']
  end

theorem sq_matrix_left_distrib {A : Type} [semiring A] {m : ℕ} (M N O : matrix A m m) :
         mul M (m_add N O) = m_add (mul M N) (mul M O) :=
  begin
    rewrite [↑mul, ↑m_add],
    repeat (apply funext; intros),
    rewrite [↑c_dot, ↑transpose, ↑row_of, ↑col_of, ↑c_ith, -Suml_add],
    congruence,
    apply funext,
    intro,
    rewrite left_distrib
  end

theorem sq_matrix_right_distrib {A : Type} [semiring A] {m : ℕ} (M N O : matrix A m m) :
         mul (m_add N O) M = m_add (mul N M) (mul O M) :=
  begin
    rewrite [↑mul, ↑m_add],
    repeat (apply funext; intros),
    rewrite [↑c_dot, ↑transpose, ↑row_of, ↑col_of, ↑c_ith, -Suml_add],
    congruence,
    apply funext,
    intro,
    rewrite right_distrib
  end

definition m_square_ring [instance] [reducible] (A : Type) [ring A] (m : ℕ) : ring (matrix A m m) :=
  ⦃ring, m_left_module A m m,
   mul := λ B C, mul B C,
   mul_assoc := λ B C D, eq.symm !m_mul_assoc,
   one := sq_matrix_id A m,
   one_mul := sq_matrix_one_mul,
   mul_one := sq_matrix_mul_one,
   left_distrib := sq_matrix_left_distrib,
   right_distrib := by intros; apply sq_matrix_right_distrib⦄

end matrix_arith_square

/-
section test
open list rat int  -- why aren't rats pretty printing right?
definition c1 : cvector ℕ  _ := cvector_of_list [3, 4, 2]
definition c2 : rvector ℕ _ := rvector_of_list [1, 0, 2]

definition f1 : fin 2 := fin.mk 1 dec_trivial

definition m1 : matrix ℤ 2 2 := λ a b, fin.val a + fin.val b

eval col_of m1 (fin.mk 1 dec_trivial)

definition m2 : matrix ℤ 2 2 := λ a b, fin.val a * fin.val b + 3

definition m10 : matrix ℕ 10 10 := λ a b, fin.val a * fin.val b + 3

definition prd := m1 * m2

definition prd' := (m1 * m2) + 3
eval prd f1 f1
eval (m1 * m2) f1 f1
eval (3 : matrix ℤ 2 2) f1 !fin.zero

example : has_mul (matrix ℤ 2 2) := _
check m1 * m2
eval ((m1 * m2) )

eval c_dot c1 (transpose c2)

example : row_of c2 !fin.zero !fin.zero (fin.mk 1 dec_trivial) = c2 !fin.zero (fin.mk 1 dec_trivial) := rfl

example : row_of c2 !fin.zero = c2 := rfl

eval (c2 ⬝ c1) !fin.zero !fin.zero

--example : m10 * !sq_matrix_id = m10 := dec_trivial

definition poly_sum (x : ℕ) := Suml (upto 10) (λ a, (a + 3) * x)

example (b : ℕ) : Suml [b, b] (λ a, a) = 0 + b + b := rfl

--definition lin_poly (x : ℕ → ℕ) := 0 + 5 * x 0 + 2 * x 1 + 3 * x 2 + 11 * x 3

definition lin_poly (x : ℕ → ℕ) := 0 + 11 * x 3 + 3 * x 2 + 2 * x 1 + 5 * x 0

definition coeff_row : rvector ℕ _ := rvector_of_list [5, 2, 3, 11]

open fin
definition var_row (x : ℕ → ℕ) : rvector ℕ 4 := λ i j, x j

example (x : ℕ → ℕ) : r_dot coeff_row (var_row x) = lin_poly x := rfl

definition xs (x : ℕ) : rvector ℕ 10 := λ a b, x

example (x : ℕ) : r_dot (row_of m10 (fin.mk 1 dec_trivial)) (xs x) = poly_sum x := rfl

definition mep : rvector ℕ 0 := λ a b, 2
definition map : matrix ℕ 0 3 := λ a b, 1

eval (mep ⬝ map) !fin.zero !fin.zero

end test-/

end matrix
