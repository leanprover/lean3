import data.string

definition nat_to_string : nat -> string
| nat_to_string nat.zero := "zero"
| nat_to_string (nat.succ _) := "not_zero"

definition main : string :=
    nat_to_string nat.zero
