import native.internal
import init.meta.format
import init.meta.expr
import init.string
import system.IO
import system.result
import native.ir
import native.format
import native.builtin
import native.util
import init.state

namespace cf

@[reducible] meta def cf_state :=
  nat

@[reducible] meta def cf_monad :=
  state cf_state

meta def trace_cf (s : string) : cf_monad unit :=
  trace s (fun u, return u)

private meta def cf_case (action : expr -> cf_monad expr) (e : expr) : cf_monad expr := do
  under_lambda (fun e', action e') e

private meta def cf_cases_on (head : expr) (args : list expr) (cf : expr -> cf_monad expr) : cf_monad expr :=
  match args with
  | [] := return $ mk_call head []
  | (scrut :: cases) := do
    trace_cf "inside cases on",
    cases' <- monad.mapM (cf_case cf) cases,
    return $ mk_call head (scrut :: cases')
  end

meta def cf' : expr -> cf_monad expr
| (expr.elet n ty val body) :=
  expr.elet n ty val <$> (cf' body)
| (expr.app f arg) := do
  trace_cf "processing app",
  let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
   in if is_cases_on fn
   then cf_cases_on fn args cf'
   else return (mk_call (expr.const `native_compiler.return []) [(expr.app f arg)])
| e := return $ expr.app (expr.const `native_compiler.return []) e

meta def init_state : cf_state := 0

end cf

meta def cf (e : expr) : expr :=
  trace ("cf: " ++ to_string e)
  (fun u, let res := prod.fst $ (cf.cf' e) cf.init_state
    in (trace $ "cf_done :" ++ to_string res) (fun u, res))

