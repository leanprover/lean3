import data.string

constant RealWorld : Type
constant raw_string : Type

axiom string_to_raw_string : RealWorld -> string -> prod RealWorld raw_string
axiom raw_print : RealWorld -> raw_string -> prod RealWorld unit

attribute string_to_raw_string [extern]
attribute raw_print [extern]
--noncomputable definition print_string (s : string) :=
--    raw_print (string_to_raw_string s)

--definition nat_to_string : nat -> string
--| nat_to_string nat.zero := "zero"
--| nat_to_string (nat.succ _) := "not_zero"

-- We say this is noncomputable, because we can't evaluate side-effecting
-- programs at compile time, when extracted this will run.
--noncomputable definition main : unit :=
--    print_string (nat_to_string nat.zero)
