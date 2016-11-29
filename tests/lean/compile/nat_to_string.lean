import data.string

inductive MyNat : Type :=
    | Zero : MyNat
    | Succ : MyNat -> MyNat

inductive RealWorld : Type :=
    | mk : RealWorld

constant raw_string : Type

constant string_to_raw_string : RealWorld -> string -> prod RealWorld raw_string
constant raw_print : RealWorld -> raw_string -> prod RealWorld unit

attribute string_to_raw_string [extern]
attribute raw_print [extern]

definition print_string (s : string) : prod RealWorld unit :=
    prod.rec_on (string_to_raw_string RealWorld.mk s)
        (fun rw rs, raw_print rw rs)

definition nat_to_string : MyNat -> string
    | nat_to_string MyNat.Zero := "zero"
    | nat_to_string (MyNat.Succ _) := "not_zero"

-- We say this is noncomputable, because we can't evaluate side-effecting
-- programs at compile time, when extracted this will run.
definition main : prod RealWorld unit :=
    print_string (nat_to_string MyNat.Zero)
