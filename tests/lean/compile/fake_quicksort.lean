import system.io
import data.list
import data.nat

open list
open nat

definition less_than : nat -> nat -> bool
| less_than nat.zero (nat.succ _) := bool.tt
| less_than (nat.succ n) (nat.succ m) := less_than n m
| less_than _ _ := bool.ff

definition quicksort : list nat -> list nat
| quicksort [] := []
| quicksort (x :: xs) :=
   let smaller := filter (fun (y : nat), x < y) xs in
   let bigger  := filter (fun y, y > x) xs in
   smaller ++ [x] ++ bigger 

definition main : IO unit :=
  print_line (quicksort [5,4,3,2,1,6])

