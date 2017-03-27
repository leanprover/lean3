import system.io
import system.process
import .solvers.z3
import .syntax
import .builder

meta def smt2 [io.interface] (build : smt2.builder unit) : io string := do
    z3 ← z3_instance.start,
    io.put_str (to_string $ to_fmt build),
    res ← z3^.raw (to_string $ to_fmt build),
    io.put_str res,
    return res

open tactic
open smt2
open smt2.builder

#check local_context

meta def reflect_prop (e : expr) : tactic (builder unit) := do
    p ← is_prop e,
    if p
    then do
        tactic.trace e,
        n <- mk_fresh_name,
        return $ declare_const (to_string n) "Bool"
    else return (return ())

#check @monad.sequence

meta def reflect_context : tactic (builder unit) := do
    ls <- local_context,
    bs <- monad.mapm reflect_prop ls,
    return $ list.foldl (fun (a b : builder unit), a >> b) (return ()) bs

meta def reflect : tactic unit := do
    tgt ← target,
    b ← reflect_context,
    str ← tactic.run_io (fun ioi, @smt2 ioi b),
    tactic.trace str,
    return ()

-- meta def reflect (: tactic (smt2.builder unit) := do
--   tgt ← target,
--   local_context
