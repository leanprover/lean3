import system.io

definition pair_string : prod string string :=
    ("pair1", "pair2")

definition main : IO unit :=
 (print_string (prod.pr1 pair_string))
         -- (fun u, print_string (prod.pr2 pair_string))
