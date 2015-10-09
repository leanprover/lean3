import algebra.ring -- has_add, has_one, ... will be moved to init in the future
open algebra

variable {A : Type}

/-structure add_numeral_struct [class] (A : Type) extends has_add A :=
  (add_comm : ∀ a b : A, add a b = add b a)
  (add_assoc : ∀ a b c : A, add (add a b) c = add a (add b c))-/

structure add_num_struct [class] (A : Type) extends comm_ring A

definition b [class] (A : Type) := A
--open add_numeral_struct
definition zero [s : add_num_struct A] : A :=
has_zero.zero A

definition one [s : add_num_struct A] : A :=
has_one.one A

definition add [s : add_num_struct A] : A → A → A :=
has_add.add

definition add1 [s : add_num_struct A] : A → A :=
λ a, a + one

definition bit0 [s : add_num_struct A] (a : A) : A :=
 a + a--add a a

definition bit1 [s₁ : add_num_struct A] (a : A) : A :=
 a + a + one --add (add a a) one

theorem add_comm_four [s : add_num_struct A] (a b : A) : a + a + (b + b) = (a + b) + (a + b) :=
  by rewrite [-add.assoc at {1}, add.comm, {a + b}add.comm at {1}, *add.assoc]

theorem add_comm_middle [s : add_num_struct A] (a b c : A) : a + b + c = a + c + b := sorry

theorem bit0_add_bit0 [s : add_num_struct A] (a b : A) : bit0 a + bit0 b = bit0 (a + b) :=
--add (bit0 a) (bit0 b) = bit0 (add a b) :=
  !add_comm_four

theorem bit0_add_bit0_helper [s : add_num_struct A] (a b t : A) (H : a + b = t) :
        bit0 a + bit0 b = bit0 t :=
  by rewrite -H; apply bit0_add_bit0

theorem bit1_add_bit0 [s : add_num_struct A] (a b : A) : bit1 a + bit0 b = bit1 (a + b) :=
  begin
    rewrite [↑bit0, ↑bit1, add_comm_middle], congruence, apply add_comm_four
  end

theorem bit1_add_bit0_helper [s : add_num_struct A] (a b t : A) (H : a + b = t) :
        bit1 a + bit0 b = bit1 t :=
  by rewrite -H; apply bit1_add_bit0

theorem bit0_add_bit1 [s : add_num_struct A] (a b : A) : bit0 a + bit1 b = bit1 (a + b) :=
  by rewrite [{bit0 a + _}add.comm, {a + _}add.comm]; apply bit1_add_bit0

theorem bit0_add_bit1_helper [s : add_num_struct A] (a b t : A) (H : a + b = t) : bit0 a + bit1 b = bit1 t :=
  by rewrite -H; apply bit0_add_bit1

theorem bit1_add_bit1 [s : add_num_struct A] (a b : A) : bit1 a + bit1 b = bit0 (add1 (a + b)) :=
  begin
    rewrite ↑[bit0, bit1, add1],
    apply sorry
  end

theorem bit1_add_bit1_helper [s : add_num_struct A] (a b t : A) (H : add1 (a + b) = t) : bit1 a + bit1 b = bit0 t :=
  begin rewrite -H, apply bit1_add_bit1 end

theorem bin_add_zero [s : add_num_struct A] (a : A) : a + zero = a := !add_zero

theorem bin_zero_add [s : add_num_struct A] (a : A) : zero + a = a := !zero_add

theorem one_add_bit0 [s : add_num_struct A] (a : A) : one + bit0 a = bit1 a :=
  begin rewrite ↑[bit0, bit1], rewrite add.comm end

theorem bit0_add_one [s : add_num_struct A] (a : A) : bit0 a + one = bit1 a := rfl

theorem bit1_add_one [s : add_num_struct A] (a : A) : bit1 a + one = add1 (bit1 a) := rfl

theorem bit1_add_one_helper [s : add_num_struct A] (a t : A) (H : add1 (bit1 a) = t) : bit1 a + one = t :=
  by rewrite -H

theorem one_add_bit1 [s : add_num_struct A] (a : A) : one + bit1 a = add1 (bit1 a) := !add.comm

theorem one_add_bit1_helper [s : add_num_struct A] (a t : A) (H : add1 (bit1 a) = t) : one + bit1 a = t :=
  by rewrite -H; apply one_add_bit1

theorem add1_bit0 [s : add_num_struct A] (a : A) : add1 (bit0 a) = bit1 a :=
  rfl

theorem add1_bit1 [s : add_num_struct A] (a : A) : add1 (bit1 a) = bit0 (add1 a) :=
  begin
    rewrite ↑[add1, bit1, bit0],
    rewrite [add.assoc, add_comm_four]
  end

theorem add1_bit1_helper [s : add_num_struct A] (a t : A) (H : add1 a = t) : add1 (bit1 a) = bit0 t :=
  by rewrite -H; apply add1_bit1

theorem add1_one [s : add_num_struct A] : add1 (one : A) = bit0 one :=
  rfl

theorem add1_zero [s : add_num_struct A] : add1 (0 : A) = one :=
  begin
    rewrite [↑add1, zero_add]
  end

theorem one_add_one [s : add_num_struct A] : (one : A) + one = bit0 one :=
  rfl

theorem subst_into_sum [s : add_num_struct A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr) (prt : tl + tr = t) :
        l + r = t :=
   by rewrite [prl, prr, prt]

theorem mk_cong (op : A → A) (a b : A) (H : a = b) : op a = op b :=
  by congruence; exact H

theorem mk_eq (a : A) : a = a := rfl

-- variables [s : add_num_struct A]
-- include s
 --set_option pp.all true
-- check bit1 (bit0 (one : A))

--example : (one : A) = (one : A) := begin norm_num end

--example : bit1 (one : A) = (one : A) := begin norm_num end

--example : bit0 (bit0 (one : A)) + bit0 (one : A) = (one : A) := begin norm_num end
