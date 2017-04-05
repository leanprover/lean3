import system.io
import .builder
import .syntax
import .solvers.z3

inductive smt2.response
| sat
| unsat
| other : string → smt2.response

meta def parse_smt2_result (str : string) : smt2.response :=
if str = "sat\n"
then smt2.response.sat
else if str = "unsat\n"
then smt2.response.unsat
else smt2.response.other str

-- should probably abstract over solvers
meta def smt2 [io.interface] (build : smt2.builder unit) : io smt2.response :=
do z3 ← z3_instance.start,
io.put_str (to_string $ to_fmt build),
res ← z3.raw (to_string $ to_fmt build),
return $ parse_smt2_result res
