import system.io
import system.process

open process

variable [io.interface]

def spawn [ioi : io.interface] : process → io (child io.handle) :=
    io.interface.process^.spawn

meta def main : io unit := do
    let p : process := { cmd := "echo", args := ["Hello World"] },
    child <- spawn p,
    let outh := child^.stdout,
     
    return ()

#eval main
