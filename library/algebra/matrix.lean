import data.real data.tuple data.fin algebra.field data.list
open nat  tuple eq.ops rat -- list

namespace matrix

definition matrix (A : Type) [field A] (m n : ℕ) := fin m → fin n → A

definition rvector (A : Type) [field A] (n : ℕ) := matrix A 1 n

definition cvector (A : Type) [field A] (m : ℕ) := matrix A m 1

-- useful for testing
definition cvector_of_list {A : Type} [field A] (l : list A) : cvector A (list.length l) :=
  λ i j, list.ith l (fin.val i) !fin.val_lt

definition rvector_of_list {A : Type} [field A] (l : list A) : rvector A (list.length l) :=
  λ i j, list.ith l (fin.val j) !fin.val_lt

section
variable {A : Type}
variable [linear_ordered_field A]
variables {m n k : ℕ}

definition col_of (M : matrix A m n) (j : fin n) : cvector A m := λ a b, M a j

definition row_of (M : matrix A m n) (i : fin m) : rvector A n := λ a b, M i b

definition r_ith (v : rvector A n) (i : fin n) := v !fin.zero i

definition c_ith (v : cvector A m) (i : fin m) := v i !fin.zero

definition nonneg (M : matrix A m n) := ∀ i j, M i j ≥ 0

definition r_dot (u v : rvector A n) := Suml (fin.upto n) (λ i, r_ith u i * r_ith v i)

definition c_dot (u v : cvector A m) := Suml (fin.upto m) (λ i, c_ith u i * c_ith v i)

-- generalize this to transpose and remove coercion
definition cvector_of_rvector [coercion] (u : rvector A n) : cvector A n := λ i j, u !fin.zero i

definition mul (M : matrix A m n) (N : matrix A n k) : matrix A m k :=
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

theorem Suml_assoc {B C : Type} (la : list B) (lb : list C) (f : B → C → A) :
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

theorem big_sum_dist_left (a : A) {T : Type} (f : T → A) (l : list T) :
        a * Suml l f = Suml l (λ k, a * f k) :=
  begin
    induction l with h tt ih,
    rewrite [Suml_nil, mul_zero],
    rewrite [*Suml_cons, left_distrib, ih]
  end

theorem big_sum_dist_right (a : A) {T : Type} (f : T → A) (l : list T) :
         Suml l f * a= Suml l (λ k, f k * a) :=
  begin
    induction l with h tt ih,
    rewrite [Suml_nil, zero_mul],
    rewrite [*Suml_cons, right_distrib, ih]
  end

theorem Suml_nonneg_of_nonneg {T : Type} (l : list T) (f : T → A)
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

theorem Suml_le_of_le {T : Type} (l : list T) (f g : T → A) (H : ∀ t : T, f t ≤ g t) :
        Suml l f ≤ Suml l g :=
  begin
    induction l,
    {rewrite *Suml_nil, apply le.refl},
    {rewrite *Suml_cons,
    apply add_le_add,
    apply H,
    assumption}
  end

theorem inner_sum_assoc {S T : Type} (l1 : list S) (l2 : list T) (f : S → A) (g : S → T → A) :
        Suml l1 (λ s, f s * Suml l2 (λ t, g s t)) = Suml l1 (λ s, Suml l2 (λ t, f s * g s t)) :=
  begin
    congruence,
    apply funext,
    intro s,
    rewrite big_sum_dist_left
  end

-- clean this up...
theorem dot_mul_assoc (y : rvector A m) (M : matrix A m n) (x : cvector A n) :
        y ⬝ (M ⬝ x) = (y ⬝ M) ⬝ x :=
  begin
    rewrite ↑mul,
    repeat (apply funext; intro),
    rewrite [fin_one_eq_zero x_1, fin_one_eq_zero x_2, ↑c_dot, ↑c_ith, *row_of_rvector, *col_of_cvector],
    rewrite [inner_sum_assoc, Suml_assoc],
    congruence,
    apply funext,
    intro b,
    unfold cvector_of_rvector,
    rewrite big_sum_dist_right,
    congruence,
    apply funext,
    intro b,
    unfold row_of, unfold col_of,
    rewrite *mul.assoc
  end

theorem cvector_of_rvector_nonneg_of_nonneg {u : rvector A n} (Hu : nonneg u) : nonneg (cvector_of_rvector u) :=
  λ i j, !Hu

theorem c_ith_cvector_of_rvector_eq_c_ith (u : rvector A n) (i : fin n) :
        c_ith (cvector_of_rvector u) i = r_ith u i :=
  rfl

theorem c_dot_nonneg_of_nonneg (u v : cvector A m) (Hu : nonneg u) (Hv : nonneg v) : c_dot u v ≥ 0 :=
  begin
    unfold c_dot,
    apply Suml_nonneg_of_nonneg,
    intros,
    apply mul_nonneg,
    apply Hu,
    apply Hv
  end

theorem row_of_nonneg_of_nonneg {M : matrix A m n} (HM : nonneg M) (i : fin m) : nonneg (row_of M i) :=
  λ a b, !HM

theorem col_of_nonneg_of_nonneg {M : matrix A m n} (HM : nonneg M) (i : fin n) : nonneg (col_of M i) :=
  λ a b, !HM

theorem mul_nonneg_of_nonneg (M : matrix A m n) (N : matrix A n k) (HM : nonneg M) (HN : nonneg N) :
        nonneg (M ⬝ N) :=
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

theorem farkas_rl (M : matrix A m n) (b : cvector A m)
        (H : ∃ y : rvector A m, nonneg (y ⬝ M) ∧ (y ⬝ b) !fin.zero !fin.zero < 0) :
        ¬ ∃ x : cvector A n, nonneg x ∧ M ⬝ x = b :=
  begin
    intro HexX,
    cases HexX with x Hx,
    cases Hx with Nx Mxb,
    cases H with y Hy,
    cases Hy with NA Nmyb,
    rewrite [-Mxb at Nmyb, dot_mul_assoc at Nmyb],
    apply not_le_of_gt Nmyb,
    apply mul_nonneg_of_nonneg,
    repeat assumption
  end


/-
 This is the useful formulation of the above for proving unsat:
 If you can find a nonnegative row vector c such that c ⬝ M = 0 and c ⬝ b < 0,
   then the system M ⬝ x ≤ b is unsat.
-/
theorem farkas_rl' (M : matrix A m n) (b : cvector A m)
        (H : ∃ c : rvector A m, nonneg c ∧ c ⬝ M = (λ x y, (0 : A)) ∧ (c ⬝ b) !fin.zero !fin.zero < 0) :
        ¬ ∃ x : cvector A n, ∀ i, (M ⬝ x) i !fin.zero ≤ c_ith b i :=
  begin
    intro HexX,
    cases HexX with x Hx,
    cases H with c Hc,
    cases Hc with Hcn Hc,
    cases Hc with HcM Hcb,
    have H : c ⬝ (M ⬝ x) = (λ a b, 0), begin
      rewrite [dot_mul_assoc, HcM, ↑mul],
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

end
check farkas_rl
end matrix
