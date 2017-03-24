import system.io
import system.process
import system.read
import data.buffer

open process

structure z3_instance [io.interface] : Type :=
    (process : child io.handle)

def spawn [ioi : io.interface] : process → io (child io.handle) :=
    io.interface.process^.spawn

def z3_instance.start  [io.interface] : io z3_instance := do
    let proc : process := {
       cmd := "z3",
       args := ["-smt2", "-in"],
       stdin := stdio.piped,
       stdout := stdio.piped
    },
    io.put_str "above mk instance",
    z3_instance.mk <$> spawn proc

def z3_instance.raw [io.interface] (z3 : z3_instance) (cmd : string) : io string := do
    let z3_stdin := z3^.process^.stdin,
    let z3_stdout := z3^.process^.stdout,
    -- do we buffer the writes here?
    let cs := cmd^.reverse^.to_buffer,
    io.fs.write z3_stdin cs,
    res <- io.fs.read z3_stdout 1024,
    return res^.to_string

    -- process.pipe.write stdin (mk_array 1 (char.of_nat 0)),
    -- read_to_string stdout
