import .io

-- class has_read (R : Type) :=
--   (read : forall {n : nat}, R → array char n → io (nat × array char n))

-- private meta def read_to_string'
--     {n : nat}
--     {R : Type} [has_read R] (resource : R)
--     : array char n → string → io string := fun buffer output, do
--     (bytes_read, buffer') <- has_read.read resource buffer,
--     if bytes_read = 0
--     then return output
--     else do
--         let new_output : string := output ++ (list.taken bytes_read buffer'^.to_list),
--         read_to_string' buffer' new_output

-- meta def read_to_string {R : Type} [has_read R] (resource : R) : io string := do
--     str <- read_to_string' resource (mk_array 256 #"C") "",
--     return str^.reverse
