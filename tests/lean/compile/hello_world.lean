import system.io

definition main : IO unit :=
    bind (print_string "Hello Lean!") (fun x, print_string "Hello Again!")
