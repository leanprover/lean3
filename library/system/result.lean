namespace system

print inductive sum

inductive result : Type -> Type -> Type
| err : Π {E R}, E -> result E R
| ok : Π {E R}, R -> result E R

inductive resultT (M : Type -> Type) (E A : Type)
| run : M (result E A) → resultT

-- TODO: elaborator is still underway, eventually clean these up, hacking around elab bugs
definition unwrap_or : Π {E T : Type}, result E T -> T -> T
| E T (result.err _) default := default
| _ T (result.ok t) _ := t

definition result.map : Π {E T U : Type}, (T → U) → result E T → result E U
| E T U f (result.err e) := result.err e
| E T U f (result.ok t) := result.ok (f t)

definition result.and_then : Π {E T U : Type}, result E T → (T -> result E U) → result E U
| E T U (result.err e) _ := result.err e
| E T U (result.ok t) f := f t

attribute [instance]
definition result_functor (E : Type) : functor (result E) :=
{| functor, map := @result.map E |}

definition result.seq : Π {E T U : Type}, result E (T → U) -> result E T → result E U
| E T U f t := result.and_then f (fun f', result.and_then t (fun t', result.ok (f' t')))

attribute [instance]
definition result_applicative (E : Type) : applicative (result E) :=
{| applicative,
pure := @result.ok E,
map := @result.map E,
seq := @result.seq E |}

attribute [instance]
definition result_monad (E : Type) : monad (result E) :=
{| monad,
map := @result.map E,
ret := @result.ok E,
bind := @result.and_then E |}

end system
