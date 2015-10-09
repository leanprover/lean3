import algebra.numeral algebra.ring
open algebra

variable {A : Type}
variable [s : add_num_struct A]
include s

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
