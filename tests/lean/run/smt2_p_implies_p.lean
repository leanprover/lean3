import tools.smt2

example (P : Prop) : P → P :=
begin
    intros,
    z3 $ "/tmp/P.smt2"
end
