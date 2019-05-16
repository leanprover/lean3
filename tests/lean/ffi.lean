import system.io
import system.foreign

namespace tactic

open environment

meta def load_foreign_object (n : name) (str : string) : tactic unit :=
updateex_env $ λ env, pure $ env.load_foreign_object n str


end tactic
open tactic foreign

def main : unit → unit → unit := λ _, id

run_cmd
do
   unsafe_run_io $ do
   { io.env.get_cwd >>= io.print_ln,
     b ← io.fs.dir_exists "vm_dynload",
     io.env.set_cwd "vm_dynload",
     b ← io.fs.file_exists "some_file.so",
     if b then io.fs.remove "some_file.so" else pure (),
     (io.cmd { cmd := "make", args := ["some_file.so"] }) >>= io.print_ln },
   load_foreign_object `foo "vm_dynload/some_file.so",
   -- bind_foreign_symbol `foo `main 2 "main",
   return ()

run_cmd trace "\nnext!\n"

@[ffi foo]
constant my_fun : uint_32 → int_64 → int_64


#eval my_fun 7 3
