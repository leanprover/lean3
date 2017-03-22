import system.io
import system.process

meta structure z3_instance :=
    (process : process.child)

meta def z3_instance.start : io z3_instance := do
    builder <- process.builder.new "z3",
    builder^.arg "-smt2",
    builder^.arg "-in",
    builder^.stdin process.stdio.piped,
    builder^.stdout process.stdio.piped,
    z3_instance.mk <$> builder^.spawn

meta def read_to_string'
    {n : nat}
    (buffer : array char n)
    (pipe : process.pipe process.pipe.mode.read)
    : string → io string := fun output, do
    io.put_str "about to read",
    bytes_read <- pipe^.read buffer,
    io.put_str "after read",
    io.put_ln bytes_read,
    if bytes_read = 0
    then return output
    else do
        let new_output : string := output ++ (list.taken bytes_read buffer^.to_list),
        io.put_ln new_output,
        read_to_string' new_output

meta def read_to_string (pipe : process.pipe process.pipe.mode.read) : io string := do
    let buf := mk_array 256 #"C",
    read_to_string' buf pipe ""

meta def z3_instance.raw (z3 : z3_instance) (cmd : string) : io.result string := do
    stdin <- z3^.process^.stdin,
    stdout <- z3^.process^.stdout,
    -- do we buffer here?
    let cs := process.array.from_string cmd,
    process.pipe.write stdin cs,
    process.pipe.write stdin (mk_array 1 (char.of_nat 0)),
    read_to_string stdout
