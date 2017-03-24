import system.io
import system.process
import .solvers.z3
import .syntax
import .builder

meta def smt2 [io.interface] (build : smt2.builder unit) : io string := do
    z3 <- z3_instance.start,
    io.put_str (to_string $ to_fmt build),
    res <- z3^.raw (to_string $ to_fmt build),
    io.put_str res,
    return res
