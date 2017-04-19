import tools.smt2

lemma uninterpreted_Props :
    forall (f g : int → Prop)
           (x y z : int)
           (Heq : forall x, f x = g x),
        f ((x + y) +z) = g (z + (y + x)) :=
begin
    intros, z3
end

lemma uninterpreted_Props_fail :
    forall (f g : int → Prop)
           (x y z : int)
           (Heq : forall x, f x = g x),
        f ((x + y) +z) = g (z + y) :=
begin
    intros, z3
end

lemma uninterpreted_functions :
    forall (f g : int → int)
           (x y z : int)
           (Heq : forall x, f x = g x),
        f ((x + y) +z) = g (z + (y + x)) :=
begin
    intros, z3
end

lemma uninterpreted_functions_mixed_sorts :
    forall (f g : Prop → int → int)
           (x y z : int)
           (Heq : forall x y, f x y = g x y),
        f (x < 0) ((x + y) +z) = g (x < 0) (z + (y + x)) :=
begin
    intros, z3 $ some "/tmp/uninterp.smt2"
end
