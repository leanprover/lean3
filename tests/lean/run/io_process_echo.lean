import system.io
import system.process

open process

variable [io.interface]

def spawn [ioi : io.interface] : process → io (child io.handle) :=
    io.interface.process^.spawn

meta def main : io unit := do
  out <- io.cmd "echo" ["Hello World!"],
  io.put_str out,
  return ()

#eval main
