
namespace tactic

open environment

meta def load_foreign_object (n : name) (str : string) : tactic unit :=
updateex_env $ λ env, pure $ env.load_foreign_object n str

meta def bind_foreign_symbol (fo fn : name) (arity : ℕ) (sym : string) : tactic unit :=
updateex_env $ λ env, pure $ env.bind_foreign_symbol fo fn arity sym

end tactic
open tactic

def main : unit → unit → unit := λ _, id

run_cmd
do load_foreign_object `foo "/Users/simon/lean/lean-master/tests/lean/vm_dynload/some_file.so",
   bind_foreign_symbol `foo `main 2 "main",
   return ()

#eval main () ()
