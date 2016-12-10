import system.io

def for {A : Type} : ℕ → A → (ℕ → A → A) -> A
| 0 default _ := default
| (n + 1) default f := for n (f n default) f

def main : io unit :=
  put_str_ln $ for 10 0 (fun i sum, sum + i)
