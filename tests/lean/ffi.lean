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
   { b ← io.fs.dir_exists "vm_dynload",
     io.env.set_cwd "vm_dynload",
     io.catch (io.fs.remove "some_file.so") (λ _, pure ()),
     io.catch (io.fs.remove "some_file.o") (λ _, pure ()),
     (io.cmd { cmd := "make", args := ["some_file.so"] }) >>= io.print_ln,
     io.env.set_cwd ".." },
   load_foreign_object `foo "./vm_dynload/some_file.so",
   return ()

run_cmd trace "\nnext!\n"

@[ffi foo]
constant my_fun : uint_32 → int_64 → int_64


#eval my_fun 7 3
