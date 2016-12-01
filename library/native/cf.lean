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
import native.pass
import native.procedure
import init.state

namespace cf

@[reducible] meta def cf_state :=
  nat

@[reducible] meta def cf_monad :=
  state cf_state

meta def trace_cf (s : string) : cf_monad unit :=
  trace s (fun u, return u)

meta def fresh_name : cf_monad name := do
  count <- state.read,
  -- need to replace this with unique prefix as per our earlier conversation
  n <- pure $ name.mk_numeral (unsigned.of_nat count) `_anf_,
  state.write (count + 1),
  return n

private meta def cf_case (action : expr -> cf_monad expr) (e : expr) : cf_monad expr := do
  under_lambda fresh_name (fun e', action e') e

private meta def cf_cases_on (head : expr) (args : list expr) (cf : expr -> cf_monad expr) : cf_monad expr :=
  match args with
  | [] := return $ mk_call head []
  | (scrut :: cases) := do
    trace_cf "inside cases on",
    cases' <- monad.mapm (cf_case cf) cases,
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

private meta def cf_transform (e : expr) : expr :=
  prod.fst $ (under_lambda cf.fresh_name cf.cf' e) cf.init_state

meta def cf : pass := {
  name := "control_flow",
  transform := fun proc, procedure.map_body cf_transform proc
}
