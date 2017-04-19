import system.io
import .builder
import .syntax
import .solvers.z3

inductive smt2.response
| sat
| unsat
| unknown
| other : string → smt2.response

meta def parse_smt2_result (str : string) : smt2.response :=
if str = "sat\n"
then smt2.response.sat
else if str = "unsat\n"
then smt2.response.unsat
else if str = "unknown\n"
then smt2.response.unknown
else smt2.response.other str

-- should probably abstract over solvers
meta def smt2 [io.interface] (build : smt2.builder unit) (log_query : option string := none) : io smt2.response :=
do z3 ← z3_instance.start,
   -- maybe we should have a primitive to go from fmt to char buffer
   let query := to_string $ to_fmt build,
   -- io.put_str (to_string $ to_fmt build),
   match log_query with
   | none := return ()
   | some fn :=
     do file ← io.mk_file_handle fn io.mode.write,
        io.fs.write file (query.reverse.to_buffer)
   end,
   res ← z3.raw (to_string $ to_fmt build),
   return $ parse_smt2_result res
