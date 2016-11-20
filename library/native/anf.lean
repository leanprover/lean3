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

@[reducible] meta def binding :=
  (name × expr × expr)

@[reducible] meta def anf_state :=
  (list (list binding) × nat)

@[reducible] meta def anf_monad :=
  state anf_state

meta def trace_anf (s : string) : anf_monad unit :=
  trace s (fun u, return u)

private meta def let_bind (n : name) (ty : expr) (e : expr) : anf_monad unit := do
  scopes <- state.read,
  match scopes with
  | ([], _) := return ()
  | ((s :: ss), count) := state.write $ (((n, ty, e) :: s) :: ss, count)
  end

private meta def mk_let : list binding -> expr -> expr
| [] body := body
| ((n, ty, val) :: es) body :=
  mk_let es (expr.elet n ty val (expr.abstract body (mk_local n)))

private meta def mk_let_in_current_scope (body : expr) : anf_monad expr := do
  (scopes, _) <- state.read,
  match scopes with
  | [] := pure $ body
  | (top :: _) := return $ mk_let top body
  end

private meta def enter_scope (action : anf_monad expr) : anf_monad expr := do
  (scopes, count) <- state.read,
  state.write ([] :: scopes, count),
  result <- action,
  bound_result <- mk_let_in_current_scope result,
  state.write (scopes, count),
  return bound_result

private meta def fresh_name : anf_monad name := do
  (ss, count) <- state.read,
  -- need to replace this with unique prefix as per our earlier conversation
  n <- pure $ name.mk_numeral (unsigned.of_nat count) `_anf_,
  state.write (ss, count + 1),
  return n

-- Hoist a set of expressions above the result of the callback
-- function.
meta def hoist
  (recursive : expr -> anf_monad expr)
  (kont : list name -> anf_monad expr) : list expr → anf_monad expr
| [] := kont []
| es := do
     ns <- monad.forM es $ (fun x, do
       value <- recursive x,
       fresh <- fresh_name,
       let_bind fresh mk_neutral_expr value,
       return fresh),
     kont ns

private meta def anf_call (head : expr) (args : list expr) (anf : expr -> anf_monad expr) : anf_monad expr := do
  hoist anf (fun ns, match ns with
  -- need to think about how to refactor this, we should get at least one back from here always
  -- this case should never happen
  | [] := return head
  | (head' :: args') := return $ mk_call (mk_local head') (list.map mk_local args')
  end) (head :: args)

private meta def anf_case (action : expr -> anf_monad expr) (e : expr) : anf_monad expr :=
  under_lambda (fun e', enter_scope (action e')) e

private meta def anf_cases_on (head : expr) (args : list expr) (anf : expr -> anf_monad expr) : anf_monad expr := do
  -- again first case should never arise
  match args with
  | [] := return $ mk_call head []
  | (scrut :: cases) := do
    trace_anf "inside cases on",
    scrut' <- anf scrut,
    cases' <- monad.mapM (anf_case anf) cases,
    return $ mk_call head (scrut' :: cases')
  end

private meta def anf' : expr -> anf_monad expr
| (expr.elet n ty val body) := do
  trace_anf "processing let",
  let_bind n ty val,
  anf' body
| (expr.app f arg) := do
  trace_anf "processing app",
  let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
   in if is_cases_on fn
      then anf_cases_on fn args anf'
      else anf_call fn args anf'
| e := return e

-- | e := return $ expr.app (expr.const `native_compiler.return []) e

meta def init_state : anf_state :=
  ([], 0)

meta def anf (e : expr) : expr :=
  trace ("anf: " ++ to_string e)
  (fun u, let res := prod.fst $ (enter_scope $ anf' e) init_state
    in (trace $ "anf_done :" ++ to_string res) (fun u, res))

