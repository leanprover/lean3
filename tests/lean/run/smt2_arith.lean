import tools.smt2

lemma arith_simple :
    forall (x y : int),
        x < y →
        x + 1 < y + 1000 :=
begin
    intros, z3
end

lemma arith_wrong :
    forall (x y : int),
        x < y →
        x + 1 < y :=
begin
    intros, z3
end

lemma lt_trans_by_z3 :
    forall (x y z : int),
        x < y →
        y < z →
        x < z :=
begin
    intros, z3
end
