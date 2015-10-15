import algebra.numeral algebra.ring
open algebra

variable {A : Type}
variable [s : add_num_struct A]
include s

definition of_pos_num [reducible] : pos_num → A
  | pos_num.one      := (one : A)
  | (pos_num.bit1 n) := bit1 (of_pos_num n)
  | (pos_num.bit0 n) := bit0 (of_pos_num n)

definition of_num [reducible] : num → A
  | num.zero    := (zero : A)
  | (num.pos n) := of_pos_num n

definition two [reducible] : A := bit0 one

definition three [reducible] : A := bit1 one

definition five [reducible] : A := bit1 (bit0 one)

definition seven [reducible] : A := bit1 (bit1 one)

definition twentyeight [reducible] := add (add seven seven) (add seven (seven : A))

example : of_num 33 = add five (twentyeight : A) := by norm_num

example : of_num 12 = add five (seven : A) := by norm_num

example : of_num 5 = add two (three : A) := by norm_num

example : of_num 9 = add two (seven : A) := by norm_num

example : of_num 12 = add five (seven : A) := by norm_num

example : of_num 12 = add (add two three) (seven : A) := by norm_num

example : of_num 0 = (zero : A) := by norm_num

example : of_num 5 = (bit1 (bit0 (one : A))) := by norm_num

definition foo : of_num 45000000000 = add ((of_num 23000000000) : A) (of_num 22000000000) := by norm_num

example : of_num 86326116 = mul (of_num 8741) ((of_num 9876) : A) := by norm_num

-- print foo





example : (one : A) = one :=
begin norm_num end

example : add one (one : A) = bit0 one :=
begin norm_num end

example : add (add (one : A)  one) (add (add (bit1 one) (bit0 (bit0 one))) (bit0 one)) = bit1 (bit1 (bit0 one)) :=
  begin norm_num end

example : add (add (one : A)  one) (add (add (bit1 one) (bit0 (bit0 one))) (bit0 one)) = bit1 (bit1 (add one one)) :=
  begin norm_num end


example : add (bit0 (one:A)) one = bit1 one :=
begin
  norm_num
end
