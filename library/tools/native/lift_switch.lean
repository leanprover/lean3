/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.meta.format
import init.meta.expr
import init.data.string
import init.category.state

import tools.native.internal
import tools.native.ir
import tools.native.format
import tools.native.builtin
import tools.native.util
import tools.native.pass
import tools.native.config
import tools.native.ir.compiler

open native

namespace lift_switch

@[reducible] meta def lift_switch_state := nat

@[reducible] meta def lift_switch_monad :=
  state lift_switch_state

private meta def fresh_name : lift_switch_monad name := do
  count ← state.read,
  -- need to replace this with unique prefix as per our earlier conversation
  n ← pure $ name.mk_numeral (unsigned.of_nat count) `_lift_switch_,
  state.write (count + 1),
  return n

private meta def lift_case (action : expr → lift_switch_monad expr) (e : expr) : lift_switch_monad expr := do
  under_lambda fresh_name (fun e', action e') e

private meta def lift_cases_on (head : expr) (args : list expr) (lift_switch : expr → lift_switch_monad expr) : lift_switch_monad expr :=
  match args with
  | [] := return $ mk_call head []
  | (scrut :: cases) := do
    -- trace_cf "inside cases on",
    cases' ← monad.mapm (lift_case lift_switch) cases,
    return $ mk_call head (scrut :: cases')
  end

meta def collect_bindings : expr -> (list (name × expr × expr) × expr)
| (expr.elet n ty v body) :=
  let (bs, body') := collect_bindings body
  in ((n, ty, v) :: bs, body')
| e := ([], e)

-- TODO: (jroesch) fix ordering issues with binder primitives
meta def under_let (e : expr) (action : expr -> lift_switch_monad expr) : lift_switch_monad expr :=
  let (bs, body) := collect_bindings e,
      rev_bindings := list.reverse bs,
      instantiated_body := expr.instantiate_vars body (list.map (fun p, mk_local $ prod.fst p) rev_bindings)
  in mk_let rev_bindings <$> action instantiated_body

meta def lift_switch' : expr -> lift_switch_monad expr
| (expr.elet n ty (expr.app f arg) body) :=
    let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
   in do
   match app_kind fn with
   | application_kind.cases := do
        val' <- lift_switch' (expr.app f arg),
        body' <- lift_switch' (expr.instantiate_var body (mk_local n)),
        return $ mk_call (expr.const `native_compiler.assign []) [mk_local n, val', body']
   | application_kind.nat_cases := return $ mk_call (expr.const `native.assign []) []
   | _ := do
    body' <- lift_switch' (expr.instantiate_var body (mk_local n)),
    return $ expr.elet n ty (expr.app f arg) (expr.abstract_local body' n)
   end
| (expr.elet n ty (expr.macro mdef i args) body) :=
  match native.get_quote_expr (expr.macro mdef i args) with
  | some _ := do
    body' <- lift_switch' (expr.instantiate_var body (mk_local n)),
    return $ mk_call (expr.const `native_compiler.assign []) [mk_local n, (expr.macro mdef i args), body']
  | none := under_let (expr.elet n ty (expr.macro mdef i args) body) lift_switch'
  end
| (expr.elet n ty e body) :=
    under_let (expr.elet n ty e body) lift_switch'
| (expr.app f arg) := do
  let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
   in if is_cases_on fn
   then lift_cases_on fn args lift_switch'
   else return (expr.app f arg)
| e := return e

private meta def init_state : lift_switch_state := 0

meta def transform (conf : config) (arity : arity_map) (e : expr) : expr :=
  prod.fst $ (under_lambda fresh_name lift_switch' e) init_state

end lift_switch

meta def lift_switch : pass := {
  name := "lift_switch",
  transform :=
    fun conf arity_map proc, procedure.map_body (fun e, lift_switch.transform conf arity_map e) proc
}
