/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.meta.format
import init.meta.expr
import init.data.string
import init.category.state

import tools.native.ir
import tools.native.format
import tools.native.builtin
import tools.native.util
import tools.native.pass
import tools.native.procedure
import tools.native.internal
import tools.native.config

open native

namespace cf

@[reducible] meta def cf_state :=
  config × nat

@[reducible] meta def cf_monad :=
  state cf_state

/-- hello world -/
meta def when_debug (action : cf_monad unit) : cf_monad unit := do
  (config, _) ← state.read,
  if config.debug
  then action
  else return ()

-- point at the code where you can't synthesize?
-- the error behavior here seems bad if you replace the unit
-- with `u`
meta def trace_cf (s : string) : cf_monad unit :=
  when_debug (trace s (return ()))

meta def fresh_name : cf_monad name := do
  (config, count) ← state.read,
  -- need to replace this with unique prefix as per our earlier conversation
  n ← pure $ name.mk_numeral (unsigned.of_nat' count) `_anf_,
  state.write (config, count + 1),
  return n

private meta def cf_case (action : expr → cf_monad expr) (e : expr) : cf_monad expr := do
  under_lambda fresh_name (fun e', action e') e

private meta def cf_cases_on (head : expr) (args : list expr) (cf : expr → cf_monad expr) : cf_monad expr :=
  match args with
  | [] := return $ mk_call head []
  | (scrut :: cases) := do
    -- trace_cf "inside cases on",
    cases' ← monad.mapm (cf_case cf) cases,
    return $ mk_call head (scrut :: cases')
  end

meta def cf' : expr → cf_monad expr
| (expr.elet n ty val body) :=
  expr.elet n ty val <$> (cf' body)
| (expr.app f arg) := do
  -- trace_cf "processing app",
  let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
   in if is_cases_on fn
   then cf_cases_on fn args cf'
   else if `native_compiler.assign = expr.const_name fn
   then match args with
   | (n :: v :: body :: []) := do
     body' <- cf' body,
     return $ mk_call fn [n, v, body']
   | _ := return $ (expr.app f arg)
   end
   else return (mk_call (expr.const `native_compiler.return []) [(expr.app f arg)])
| e := return $ expr.app (expr.const `native_compiler.return []) e

meta def init_state : config → cf_state :=
  fun c, (c, 0)

end cf

private meta def cf_transform (conf : config) (e : expr) : expr :=
  prod.fst $ (under_lambda cf.fresh_name cf.cf' e) (cf.init_state conf)

meta def cf : pass := {
  name := "control_flow",
  transform := fun conf arity proc, procedure.map_body (fun e, cf_transform conf e) proc
}
