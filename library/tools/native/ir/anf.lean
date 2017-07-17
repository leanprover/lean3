/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.meta.format
import init.meta.expr
import init.data.string
import init.category.state

import tools.native.ir.internal
import tools.native.ir.syntax
import tools.native.ir.builtin
import tools.native.ir.util
import tools.native.ir.pass
import tools.native.config

open native

namespace anf

@[reducible] meta def anf_state :=
(arity_map × list (list binding) × nat)

@[reducible] meta def anf_monad :=
state anf_state

inductive call_type
| saturated
| under_sat
| over_sat : nat -> call_type

meta def trace_anf (s : string) : anf_monad unit :=
trace s (return ())

meta def get_call_type (n : name) (no_args : nat) : anf_monad call_type :=
do (map, _, _) <- state.read,
  match rb_map.find map n with
  | none := pure call_type.under_sat
  | some arity := do
    if arity = no_args
    then
      pure call_type.saturated
    else if no_args < arity
    then
      pure call_type.under_sat
    else
      pure (call_type.over_sat arity)
  end

meta def fresh_name : anf_monad name :=
do (arity, ss, count) ← state.read,
   n ← pure $ name.mk_numeral (unsigned.of_nat count) `_anf_,
   state.write (arity, ss, count + 1),
   return n

private meta def let_bind (n : name) (ty : expr) (e : expr) : anf_monad unit :=
do scopes ← state.read,
   match scopes with
   | (arity, [], _) := return ()
   | (arity, (s :: ss), count) := state.write $ (arity, ((n, ty, e) :: s) :: ss, count)
   end

private meta def anf_let (nm : name) (ty val body : expr) (anf : expr → anf_monad expr) : anf_monad expr :=
do fresh ← fresh_name,
   val' ← anf val,
   let_bind fresh ty val',
   anf (expr.instantiate_var body (mk_local fresh))

meta def should_abstract : binding -> bool
| (n, ty, val) :=
match val with
| (expr.app f arg) :=
  let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
  in match app_kind fn with
  | application_kind.cases := ff
  | application_kind.nat_cases := ff
  | _ := tt
  end
| (expr.macro m_def args) :=
  match native.get_quote_expr (expr.macro m_def args) with
  | some _ := ff
  | _ := tt
  end
| _ := tt
end

meta def mk_single_let (body : expr) (b : binding) : expr :=
let (n, ty, val) := b in
match val with
  | (expr.app f arg) :=
    let fn := expr.get_app_fn (expr.app f arg),
    args := expr.get_app_args (expr.app f arg)
    in match app_kind fn with
    | application_kind.cases :=
      mk_call (expr.const `native_compiler.assign []) [mk_local n, (expr.app f arg), body]
    | application_kind.nat_cases := mk_call (expr.const `native.assign []) []
    | _ := expr.elet n ty val body
    end
   | (expr.macro mdef args) :=
   match native.get_quote_expr (expr.macro mdef args) with
   | some _ := mk_call (expr.const `native_compiler.assign []) [mk_local n, (expr.macro mdef args), body]
   | _ := expr.elet n ty val body
   end
  | _ := expr.elet n ty val body
end

meta def mk_let' (bindings : list binding) (body : expr) : expr :=
list.foldr
  (fun rest elem, mk_single_let elem rest)
  (body.abstract_locals (list.map prod.fst (list.reverse (list.filter (fun b, should_abstract b = tt) bindings))))
  bindings.reverse

private meta def mk_let_in_current_scope (body : expr) : anf_monad expr :=
do (_, scopes, _) ← state.read,
   match scopes with
   | [] := pure $ body
   | (top :: _) := return $ mk_let' top body
   end

private meta def enter_scope (action : anf_monad expr) : anf_monad expr :=
do (arity, scopes, count) ← state.read,
   state.write (arity, [] :: scopes, count),
   result ← action,
   bound_result ← mk_let_in_current_scope result,
   -- this is bug prone, need lenses?
   (arity, _, count) ← state.read,
   state.write (arity, scopes, count),
   return bound_result

-- Hoist a set of expressions above the result of the callback
-- function.
meta def hoist
  (anf : expr → anf_monad expr)
  (kont : list name → anf_monad expr) : list expr → anf_monad expr
| [] := kont []
| es :=
  do ns ← monad.for es $ (fun x, do
     value ← anf x,
     if expr.is_local_constant value
     then return (expr.local_uniq_name value)
     else do
      fresh ← fresh_name,
      let_bind fresh mk_neutral_expr value,
      return fresh),
     kont ns

private meta def anf_constructor (head : expr) (args : list expr) (anf : expr → anf_monad expr) : anf_monad expr :=
hoist anf (fun args', return $ mk_call head (list.map mk_local args')) args

-- transform a call where the head expression should be anf lifted
private meta def anf_call' (head : expr) (args : list expr) (anf : expr → anf_monad expr) : anf_monad expr := do
hoist anf (λ ns,
  match ns with
  -- TODO(@jroesch): I need to think about how to refactor this.
  -- We should get at least one back from here, i.e this case should never happen
  | [] := return head
  | (head' :: args') := return $ mk_call (mk_local head') (list.map mk_local args')
  end) (head :: args)

private meta def direct_call (head : expr) (args : list expr) (anf : expr → anf_monad expr) : anf_monad expr :=
hoist anf (fun args', return $ mk_call head (list.map mk_local args')) args

private meta def anf_call (head : expr) (args : list expr) (anf : expr → anf_monad expr) : anf_monad expr := do
-- trace_anf ("anf_call: " ++ to_string head ++ to_string args),
if expr.is_constant head
then do
  type <- get_call_type (expr.const_name head) (list.length args),
  match type with
  | call_type.saturated :=
    direct_call head args anf
  | call_type.over_sat arity := do
      -- trace_anf "oversat",
    let pre_args := list.take arity args,
    let post_args := list.drop arity args,
    call_expr <- (direct_call head pre_args anf),
    anf_call' call_expr post_args anf
  | call_type.under_sat := do
    -- trace_anf "unsat",
    anf_call' head args anf
  end
else
  anf_call' head args anf

private meta def anf_case (action : expr → anf_monad expr) (e : expr) : anf_monad expr := do
under_lambda fresh_name (fun e', enter_scope (action e')) e

private meta def anf_cases_on (head : expr) (args : list expr) (anf : expr → anf_monad expr) : anf_monad expr := do
match args with
| [] := return $ mk_call head []
| (scrut :: cases) := do
  scrut' ← anf scrut,
  cases' ← monad.mapm (anf_case anf) cases,
  return $ mk_call head (scrut' :: cases')
end

private meta def anf_projection (head : expr) (args : list expr) (anf : expr → anf_monad expr) : anf_monad expr :=
match args with
| (struct :: remaining) := do
  proj_name <- fresh_name,
  proj <- anf_constructor head [struct] anf,
  let_bind proj_name mk_neutral_expr proj,
  hoist anf (fun args', return $ mk_call (mk_local proj_name) (list.map mk_local args')) remaining
-- TODO(jroesch): this should be an error, make this a result monad
| _ := anf_constructor head args anf
end

open native.application_kind

private meta def anf' : expr → anf_monad expr
| (expr.elet n ty val body) := do
  anf_let n ty val body anf'
| (expr.app f arg) := do
  let fn := expr.get_app_fn (expr.app f arg),
  let args := expr.get_app_args (expr.app f arg),
  match app_kind fn with
  | cases := anf_cases_on fn args anf'
  | nat_cases := anf_cases_on fn args anf'
  | constructor _ := anf_constructor fn args anf'
  | projection _ := anf_projection fn args anf'
  | _ := anf_call fn args anf'
  end
| e := return e

private meta def init_state (armap : arity_map) : anf_state :=
(armap, [], 0)

meta def transform (conf : config) (arity : arity_map) (e : expr) : expr :=
prod.fst $ (under_lambda anf.fresh_name (enter_scope ∘ anf') e) (init_state arity)

end anf

open anf

meta def anf : pass :=
{ name := "anf",
  transform :=
    λ conf arity_map proc, procedure.map_body (λ e, transform conf arity_map e) proc }
