inductive result (E : Type) : Type -> Type
| err : Π {R}, E -> result R
| ok : Π {R : Type}, R -> result R
