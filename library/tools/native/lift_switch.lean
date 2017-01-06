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

meta def trace_lift (s : string) : lift_switch_monad unit :=
  trace s (fun u, return u)

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
    -- I shouldn't have to do this since scrut should already be a name at this place.
    scrut' <- lift_switch scrut,
    cases' ← monad.mapm (lift_case lift_switch) cases,
    return $ mk_call head (scrut' :: cases')
  end

meta def collect_bindings : expr -> (list (name × expr × expr) × expr)
| (expr.elet n ty v body) :=
  let (bs, body') := collect_bindings body
  in ((n, ty, expr.instantiate_var v (mk_local n)) :: bs, body')
| e := ([], e)

meta def under_let_process_binding (action : expr -> lift_switch_monad expr) : binding -> lift_switch_monad binding
| (n, ty, v) := do
  v' <- action v,
  return (n, ty, v')

-- TODO: (jroesch) fix ordering issues with binder primitives
meta def under_let (e : expr) (action : expr -> lift_switch_monad expr) : lift_switch_monad expr :=
  let (bs, body) := collect_bindings e in do
      rev_bindings <- monad.mapm (under_let_process_binding action) $ list.reverse bs,
      mk_let rev_bindings <$> action body
  -- let instantiated_body := expr.instantiate_vars body (list.map (fun p, mk_local $ prod.fst p) rev_bindings)

meta def lift_switch_let (action : expr -> lift_switch_monad expr) (nm : name) (ty body : expr) : expr -> lift_switch_monad expr
| (expr.app f arg) :=
  let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
   in do
   trace_lift ("HEAD SYMBOL: " ++ to_string f),
   match app_kind fn with
   | application_kind.cases := trace ("HEADin" ++ to_string fn) (fun _, do
        val' <- action (expr.app f arg),
        body' <- action (expr.instantiate_var body (mk_local nm)),
        let res := mk_call (expr.const `native_compiler.assign []) [mk_local nm, val', body'] in
        trace (to_string res) (fun _, pure $ res))
   | application_kind.nat_cases := return $ mk_call (expr.const `native.assign []) []
   | _ := do trace_lift "HEREEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE", under_let (expr.elet nm ty (expr.app f arg) body) action
   end
| (expr.macro mdef i args) :=
  match native.get_quote_expr (expr.macro mdef i args) with
  | some _ := do
    body' <- action (expr.instantiate_var body (mk_local nm)),
    return $ mk_call (expr.const `native_compiler.assign []) [mk_local nm, (expr.macro mdef i args), body']
  | none := under_let (expr.elet nm ty (expr.macro mdef i args) body) action
  end
| e := under_let (expr.elet nm ty e body) action

print expr

meta def lift_switch' : expr -> lift_switch_monad expr
| (expr.elet n ty e body) :=
  lift_switch_let lift_switch' n ty body e
| (expr.app f arg) := do
  let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
   in if is_cases_on fn
   then do trace_lift ("in cases" ++ to_string fn), lift_cases_on fn args lift_switch'
   else do
     fn' <- lift_switch' fn,
     args' <- monad.mapm lift_switch' args,
     return (mk_call fn' args')
| e := return e


private meta def init_state : lift_switch_state := 0

meta def transform (conf : config) (arity : arity_map) (e : expr) : expr :=
  prod.fst $ (under_lambda fresh_name lift_switch' e) init_state

end lift_switch

meta def lift_switch : pass := {
  name := "lift_switch",
  transform :=
    fun conf arity_map proc,
      let proc := procedure.map_body (fun e, lift_switch.transform conf arity_map e) proc
      in trace (to_string proc) (fun u, proc)
}
