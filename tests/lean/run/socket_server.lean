import system.io

def SECRET : string := "SECRET_DATA"

meta def start_client : io io.proc.child :=
do test_dir ← io.env.get "TEST_DIR",
   (bin_dir, test_dir) ←
     return $ match test_dir with
     | some s := (s ++ "/../../../", s ++ "/")
     | none := ("", "tests/lean/run/")
     end,
   io.proc.spawn {
     cmd := bin_dir ++ "bin/lean",
     args := ["--run", test_dir ++ "socket_client.lean", "client"]
   }

meta def init : io unit :=
io.fs.remove "hello.unix" <|> return ()

meta def start_server : io (option io.net.socket) :=
do io.run_tactic $ tactic.trace "listen",
   some <$> io.net.listen "hello.unix" SECRET.length
-- Some versions of windows don't support UNIX sockets,
-- so just roll with it
   <|> return none

meta def do_server (sock : io.net.socket) : io unit :=
do io.run_tactic $ tactic.trace "accept",
   sock ← io.net.accept sock,
   io.run_tactic $ tactic.trace "send",
   io.net.send sock SECRET.to_char_buffer,
   io.run_tactic $ tactic.trace "bye"

meta def go : io unit :=
do init,
   sock ← start_server,
   match sock with
   | none := return ()
   | some sock :=
     do io.run_tactic $ tactic.trace "startup",
        c ← start_client,
        do_server sock,
        n ← io.proc.wait c,
        io.net.close sock,
        init,
        match n with
        | 0 := return ()
        | n := io.fail sformat!"exit code {n}!"
        end
    end

run_cmd (tactic.unsafe_run_io go)
