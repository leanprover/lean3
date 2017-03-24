import system.io
import system.process

open process

variable [io.interface]

def spawn [ioi : io.interface] : process → io (child io.handle) :=
    io.interface.process^.spawn

meta def main : io unit :=
    let p : process := { cmd := "echo", args := ["Hello World"] }
    in do spawn p, return ()

#eval main
