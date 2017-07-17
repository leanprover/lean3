import system.io

variable [io.interface]

def for {A : Type} : ℕ → A → (ℕ → A → A) -> A
| 0 default _ := default
| (n + 1) default f := for n (f n default) f

def main : io unit :=
  io.print $ for 10 0 (fun i sum, sum + i)

#eval main
