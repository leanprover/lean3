import .io

class has_read (R : Type) :=
  (read : forall {n : nat}, R → array char n → io nat)

-- meta def read_to_string {R : Type} [has_read R] : R → string :=
