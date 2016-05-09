import system.io

set_option trace.backend true
-- We say this is noncomputable, because we can't evaluate side-effecting
-- programs at compile time, when extracted this will run.
definition main : IO unit :=
    print_string "Hello Lean!"
