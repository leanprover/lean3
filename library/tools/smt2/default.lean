import system.io
import system.process
import .solvers.z3
import .syntax
import .builder

meta def z3 (build : smt2.builder unit) : io string := do
    z3 <- z3_instance.start,
    io.put_str (to_string $ to_fmt build),
    res <- z3^.raw (to_string $ to_fmt build),
    match res with
    | (result.error e) := do io.put_str e, return "fail"
    | (result.ok v) := do io.put_str v, return v
    end
