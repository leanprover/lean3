import system.io
import system.process
import system.read
import data.buffer

meta structure z3_instance :=
    (process : process.child)

meta def z3_instance.start : io z3_instance := do
    builder <- process.builder.new "z3",
    builder^.arg "-smt2",
    builder^.arg "-in",
    builder^.stdin process.stdio.piped,
    builder^.stdout process.stdio.piped,
    z3_instance.mk <$> builder^.spawn

meta def z3_instance.raw (z3 : z3_instance) (cmd : string) : io.result string := do
    stdin <- z3^.process^.stdin,
    stdout <- z3^.process^.stdout,
    -- do we buffer the writes here?
    let cs := cmd^.reverse^.to_buffer^.to_array,
    process.pipe.write stdin cs,
    process.pipe.write stdin (mk_array 1 (char.of_nat 0)),
    read_to_string stdout
