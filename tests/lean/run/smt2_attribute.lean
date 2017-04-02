import tools.smt2

constants f g : Prop → int → int
attribute [smt2] f
attribute [smt2] g

constants x y z : int
attribute [smt2] x
attribute [smt2] y
attribute [smt2] z

constants Heq : forall (x x' : Prop) (y : int),
    (x -> x') ->
    f x y = g x' y

attribute [smt2] Heq

lemma uninterpreted_functions_with_attr :
    f (x < 0) ((x + y) +z) = g (x < 0) (z + (y + x)) :=
begin
    intros, z3
end
