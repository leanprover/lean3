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
    (pipe : process.pipe process.pipe.mode.read)
    :  array char n → string → io string := fun buffer output, do
    (bytes_read, buffer') <- pipe^.read buffer,
    if bytes_read = 0
    then return output
    else do
        let new_output : string := output ++ (list.taken bytes_read buffer'^.to_list),
        read_to_string' buffer' new_output

meta def read_to_string (pipe : process.pipe process.pipe.mode.read) : io string := do
    str <- read_to_string' pipe (mk_array 256 #"C") "",
    return str^.reverse

meta def z3_instance.raw (z3 : z3_instance) (cmd : string) : io.result string := do
    stdin <- z3^.process^.stdin,
    stdout <- z3^.process^.stdout,
    -- do we buffer here?
    let cs := process.array.from_string cmd,
    process.pipe.write stdin cs,
    process.pipe.write stdin (mk_array 1 (char.of_nat 0)),
    read_to_string stdout
