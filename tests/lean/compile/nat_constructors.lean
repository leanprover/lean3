inductive N :=
| Z : N
| S : N -> N

definition Nadd (m : N) : N -> N
| Nadd N.Z := m
| Nadd (N.S n) := Nadd n

definition main : nat := nat.succ nat.zero
