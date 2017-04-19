import tools.smt2

example (P : Prop) (p : P) (np : not P) : 3 < 1 :=
begin
    intros,
    z3
end
