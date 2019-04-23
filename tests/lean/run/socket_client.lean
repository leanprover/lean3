import system.io

def SECRET : string := "SECRET_DATA"

meta def do_client : io unit :=
do io.proc.sleep 2,
   io.run_tactic $ tactic.trace "connect",
   sock ← io.net.connect "hello.unix",
   io.run_tactic $ tactic.trace "recv",
   key ← io.net.recv sock SECRET.length,
   io.run_tactic $ tactic.trace key,
   if buffer.to_string key = SECRET
      then return ()
      else io.fail sformat!"INCORRECT: {key.to_list}"

meta def main : io unit :=
do args ← io.cmdline_args,
   match args with
   | ["client"] := do_client
   | _ := return ()
   end