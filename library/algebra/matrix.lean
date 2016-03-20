import data.real data.tuple data.fin algebra.module data.list
open nat  tuple eq.ops rat -- list

namespace matrix

definition matrix (A : Type) (m n : ℕ) := fin m → fin n → A

definition rvector (A : Type) (n : ℕ) := matrix A 1 n

definition cvector (A : Type) (m : ℕ) := matrix A m 1

/-definition val_of_singleton_matrix [coercion] {A : Type} (M : matrix A 1 1) : A :=
  M !fin.zero !fin.zero-/

-- useful for testing
definition cvector_of_list {A : Type} (l : list A) : cvector A (list.length l) :=
  λ i j, list.ith l (fin.val i) !fin.val_lt

definition rvector_of_list {A : Type} (l : list A) : rvector A (list.length l) :=
  λ i j, list.ith l (fin.val j) !fin.val_lt

section
variable {A : Type}
variables {m n k : ℕ}

definition col_of (M : matrix A m n) (j : fin n) : cvector A m := λ a b, M a j

definition row_of (M : matrix A m n) (i : fin m) : rvector A n := λ a b, M i b

definition r_ith (v : rvector A n) (i : fin n) := v !fin.zero i

definition c_ith (v : cvector A m) (i : fin m) := v i !fin.zero

definition nonneg [weak_order A] [has_zero A] (M : matrix A m n) := ∀ i j, M i j ≥ 0

definition r_dot [semiring A] (u v : rvector A n) := Suml (fin.upto n) (λ i, r_ith u i * r_ith v i)

definition c_dot [semiring A] (u v : cvector A m) := Suml (fin.upto m) (λ i, c_ith u i * c_ith v i)

-- generalize this to transpose and remove coercion
definition cvector_of_rvector [coercion] (u : rvector A n) : cvector A n := λ i j, u !fin.zero i

definition mul [semiring A] (M : matrix A m n) (N : matrix A n k) : matrix A m k :=
  λ (a : fin m) (b : fin k), c_dot (cvector_of_rvector (row_of M a)) (col_of N b) -- why doesn't coercion work?

infix `⬝` := mul

theorem fin_one_eq_zero (x : fin 1) : x = !fin.zero :=
  begin
    induction x,
    unfold fin.zero,
    congruence,
    apply eq_zero_of_le_zero,
    apply le_of_lt_succ is_lt
  end

theorem row_of_rvector (v : rvector A n) : row_of v !fin.zero = v :=
  begin
    apply funext,
    intro x,
    unfold row_of,
    rewrite (fin_one_eq_zero x)
  end

theorem col_of_cvector (v : cvector A m) : col_of v !fin.zero = v :=
  begin
    apply funext,
    intro x,
    apply funext,
    intro y,
    unfold col_of,
    rewrite (fin_one_eq_zero y)
  end

theorem row_of_ith (M : matrix A m n) (x : fin m) (y : fin n) : (row_of M x) !fin.zero y = M x y :=
  rfl

theorem col_of_ith (M : matrix A m n) (x : fin m) (y : fin n) : (col_of M y) x !fin.zero = M x y :=
  rfl

theorem Suml_assoc [semiring A] {B C : Type} (la : list B) (lb : list C) (f : B → C → A) :
        Suml la (λ a, Suml lb (λ b, f a b))
          = Suml lb (λ b, Suml la (λ a, f a b)) :=
  begin
    induction la with h tt ih,
    induction lb with h' tt' ih',
    {rewrite [Suml_nil]},
    {rewrite [Suml_nil at *, Suml_cons, -ih', add_zero]},
    {induction lb with h' tt' ih',
    {rewrite [Suml_cons, *Suml_nil at *, ih, add_zero]},
    {rewrite [Suml_cons, ih, -Suml_add],
    congruence,
    apply funext,
    intro b,
    rewrite Suml_cons}}
  end

theorem length_cons_pos {A : Type} (h : A) (tt : list A) : 0 < list.length (list.cons h tt) :=
  begin
    apply lt_of_not_ge,
    intro H,
    let H' := list.eq_nil_of_length_eq_zero (eq_zero_of_le_zero H),
    apply !list.cons_ne_nil H'
  end

theorem big_sum_dist_left [semiring A] (a : A) {T : Type} (f : T → A) (l : list T) :
        a * Suml l f = Suml l (λ k, a * f k) :=
  begin
    induction l with h tt ih,
    rewrite [Suml_nil, mul_zero],
    rewrite [*Suml_cons, left_distrib, ih]
  end

theorem big_sum_dist_right [semiring A] (a : A) {T : Type} (f : T → A) (l : list T) :
         Suml l f * a= Suml l (λ k, f k * a) :=
  begin
    induction l with h tt ih,
    rewrite [Suml_nil, zero_mul],
    rewrite [*Suml_cons, right_distrib, ih]
  end

theorem Suml_nonneg_of_nonneg [ordered_semiring A] {T : Type} (l : list T) (f : T → A)
        (H : Π (i : ℕ) (Hi : i < list.length l), f (list.ith l i Hi) ≥ 0) : Suml l f ≥ (0 : A) :=
  begin
    induction l with h tt ih,
    rewrite Suml_nil,
    apply le.refl,
    rewrite Suml_cons,
    have Hh : f h ≥ 0, begin
      note Hl := H 0 !length_cons_pos,
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

theorem Suml_le_of_le [ordered_semiring A] {T : Type} (l : list T) (f g : T → A) (H : ∀ t : T, f t ≤ g t) :
        Suml l f ≤ Suml l g :=
  begin
    induction l,
    {rewrite *Suml_nil, apply le.refl},
    {rewrite *Suml_cons,
    apply add_le_add,
    apply H,
    assumption}
  end

theorem inner_sum_assoc [semiring A] {S T : Type} (l1 : list S) (l2 : list T) (f : S → A) (g : S → T → A) :
        Suml l1 (λ s, f s * Suml l2 (λ t, g s t)) = Suml l1 (λ s, Suml l2 (λ t, f s * g s t)) :=
  begin
    congruence,
    apply funext,
    intro s,
    rewrite big_sum_dist_left
  end

theorem Suml_distrib [semiring A] {S : Type} (l : list S) (f : S → A) (a : A) :
        Suml l (λ x, f x * a) = (Suml l f) * a :=
  begin
    induction l,
    {rewrite [*Suml_nil, zero_mul]},
    {rewrite [*Suml_cons, right_distrib], congruence, assumption}
  end

theorem m_mul_assoc [semiring A] {o p : ℕ} (M : matrix A m n) (N : matrix A n o) (O : matrix A o p) :
        M ⬝ (N ⬝ O) = (M ⬝ N) ⬝ O :=
  begin
    rewrite ↑mul,
    repeat (apply funext; intro),
    rewrite [↑c_dot, ↑c_ith, ↑row_of, ↑cvector_of_rvector, ↑col_of, inner_sum_assoc, Suml_assoc],
    congruence, apply funext, intro,
    rewrite -Suml_distrib,
    congruence, apply funext, intro,
    rewrite mul.assoc
  end

theorem cvector_of_rvector_nonneg_of_nonneg [weak_order A] [has_zero A] {u : rvector A n} (Hu : nonneg u) :
        nonneg (cvector_of_rvector u) :=
  λ i j, !Hu

theorem c_ith_cvector_of_rvector_eq_c_ith (u : rvector A n) (i : fin n) :
        c_ith (cvector_of_rvector u) i = r_ith u i :=
  rfl

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
    apply cvector_of_rvector_nonneg_of_nonneg,
    apply row_of_nonneg_of_nonneg HM,
    apply col_of_nonneg_of_nonneg HN
  end

/-
 One direction of Farkas' lemma
-/

theorem farkas_rl [ordered_semiring A] (M : matrix A m n) (b : cvector A m)
        (H : ∃ y : rvector A m, nonneg (y ⬝ M) ∧ (y ⬝ b) !fin.zero !fin.zero < 0) :
        ¬ ∃ x : cvector A n, nonneg x ∧ M ⬝ x = b :=
  begin
    intro HexX,
    cases HexX with x Hx,
    cases Hx with Nx Mxb,
    cases H with y Hy,
    cases Hy with NA Nmyb,
    rewrite [-Mxb at Nmyb, m_mul_assoc at Nmyb],
    apply not_le_of_gt Nmyb,
    apply mul_nonneg_of_nonneg,
    exact NA, exact Nx -- why doesn't assumption work here?
  end


/-
 This is the useful formulation of the above for proving unsat:
 If you can find a nonnegative row vector c such that c ⬝ M = 0 and c ⬝ b < 0,
   then the system M ⬝ x ≤ b is unsat.
-/
theorem farkas_rl' [ordered_semiring A] (M : matrix A m n) (b : cvector A m)
        (H : ∃ c : rvector A m, nonneg c ∧ c ⬝ M = (λ x y, (0 : A)) ∧ (c ⬝ b) !fin.zero !fin.zero < 0) :
        ¬ ∃ x : cvector A n, ∀ i, (M ⬝ x) i !fin.zero ≤ c_ith b i :=
  begin
    intro HexX,
    cases HexX with x Hx,
    cases H with c Hc,
    cases Hc with Hcn Hc,
    cases Hc with HcM Hcb,
    have H : c ⬝ (M ⬝ x) = (λ a b, 0), begin
      rewrite [m_mul_assoc, HcM, ↑mul],
      repeat (apply funext; intro),
      rewrite [fin_one_eq_zero, row_of_rvector, ↑c_dot],
      have Hz : (λ i, c_ith (cvector_of_rvector (λ (x : fin 1) (y : fin n), 0)) i * c_ith (col_of x x_2) i)
                  = (λ i, 0), begin
       apply funext, intro i,
       rewrite [ c_ith_cvector_of_rvector_eq_c_ith, ↑r_ith, zero_mul]
      end,
      rewrite [Hz, Suml_zero]
    end,
    have H' : (c ⬝ (M ⬝ x)) !fin.zero !fin.zero ≤ (c ⬝ b) !fin.zero !fin.zero, begin
      rewrite ↑mul at {2, 3},
      rewrite [*col_of_cvector, *row_of_rvector],
      unfold c_dot,
      apply Suml_le_of_le,
      intro t,
      apply mul_le_mul_of_nonneg_left,
      apply Hx,
      apply Hcn
    end,
    have HZ : (0 : A) < 0, from calc
        0 = (c ⬝ (M ⬝ x)) !fin.zero !fin.zero : by rewrite H
      ... ≤ (c ⬝ b) !fin.zero !fin.zero : H'
      ... < 0 : Hcb,
    exact not_lt_self _ HZ
  end

/-
 An alternate form of the above.
-/
theorem farkas_rl'' [ordered_semiring A] (M : matrix A m n) (b : cvector A m) (c : rvector A m)
        (Hcnn : nonneg c) (HcM : ∀ (x : fin n), (c ⬝ M) !fin.zero x = 0) (Hcb : (c ⬝ b) !fin.zero !fin.zero < 0) :
        ¬ ∃ x : cvector A n, ∀ i, (M ⬝ x) i !fin.zero ≤ c_ith b i :=
  begin
    apply farkas_rl',
    existsi c,
    split,
    assumption,
    split,
    repeat (apply funext; intro),
    rewrite fin_one_eq_zero,
    apply HcM,
    assumption
  end

section
open list
definition decidable_quant [instance] (P : fin n → Prop) [∀ k, decidable (P k)] : decidable (∀ k, P k) :=
  if H : all (fin.upto n) P then
    decidable.inl (λ k, have Hk : k ∈ fin.upto n, from !fin.mem_upto, of_mem_of_all Hk H)
  else
    decidable.inr (λ Hpk, H (all_of_forall (λ a Ha, Hpk a)))

definition matrix_decidable_eq [instance] [decidable_eq A] : decidable_eq (matrix A m n) :=
  λ M N : matrix A m n,
  if H : ∀ i : fin m, ∀ j : fin n, M i j = N i j then
    decidable.inl (funext (λ i, funext (λ j, H i j)))
  else
    decidable.inr (begin intro Heq, apply H, intros, congruence, exact Heq end)
end

end

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

end matrix_arith_m_n

theorem false_of_fin_zero (x : fin 0) : false :=
  have t : empty, from equiv.fn (fin.fin_zero_equiv_empty) x,
  empty.induction_on (λ c, false) t

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
theorem b_vec_dot {A : Type} [semiring A] {m : ℕ} (k : fin m) (f : fin m → A) :
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
      congruence,
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
      rewrite Hjk,
      induction k,
      unfold [lift_succ, lift]
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
    rewrite [H, b_vec_dot]
  end

theorem sq_matrix_mul_one {A : Type} [semiring A] {m : ℕ} (M : matrix A m m) : mul M (sq_matrix_id A m) = M :=
  begin
    rewrite [↑sq_matrix_id, ↑mul],
    repeat (apply funext; intro),
    rewrite [↑row_of, ↑cvector_of_rvector, ↑col_of, ↑c_dot, ↑c_ith, b_vec_dot]
  end

theorem sq_matrix_one_mul {A : Type} [semiring A] {m : ℕ} (M : matrix A m m) : mul (sq_matrix_id A m) M = M :=
  begin
    rewrite [↑sq_matrix_id, ↑mul],
    repeat (apply funext; intro),
    rewrite [↑row_of, ↑cvector_of_rvector, ↑col_of, ↑c_dot, ↑c_ith, b_vec_dot']
  end

theorem sq_matrix_left_distrib {A : Type} [ring A] {m : ℕ} (M N O : matrix A m m) :
         mul M (m_add N O) = m_add (mul M N) (mul M O) :=
  begin
    rewrite [↑mul, ↑m_add],
    repeat (apply funext; intros),
    rewrite [↑c_dot, ↑cvector_of_rvector, ↑row_of, ↑col_of, ↑c_ith, -Suml_add],
    congruence,
    apply funext,
    intro,
    rewrite left_distrib
  end

theorem sq_matrix_right_distrib {A : Type} [ring A] {m : ℕ} (M N O : matrix A m m) :
         mul (m_add N O) M = m_add (mul N M) (mul O M) :=
  begin
    rewrite [↑mul, ↑m_add],
    repeat (apply funext; intros),
    rewrite [↑c_dot, ↑cvector_of_rvector, ↑row_of, ↑col_of, ↑c_ith, -Suml_add],
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
   right_distrib := by intros; apply sq_matrix_right_distrib
  ⦄

end matrix_arith_square


section test
open list rat  -- why aren't rats pretty printing right?
definition c1 : cvector ℚ _ := cvector_of_list [3, 4, 2]
definition c2 : rvector ℚ _ := rvector_of_list [1, 0, 2]

definition m1 : matrix ℚ 2 2 := λ a b, fin.val a + fin.val b
eval col_of m1 (fin.mk 1 dec_trivial)

eval c_dot c1 (cvector_of_rvector c2)

example : row_of c2 !fin.zero !fin.zero (fin.mk 1 dec_trivial) = c2 !fin.zero (fin.mk 1 dec_trivial) := rfl

example : row_of c2 !fin.zero = c2 := rfl

eval (c2 ⬝ c1) !fin.zero !fin.zero

end test

end matrix
