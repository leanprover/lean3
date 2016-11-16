import native.internal
import init.meta.format
import init.meta.expr
import init.string
import system.IO
import system.result
import native.ir
import native.format
import native.builtin
import init.state

@[reducible] meta def anf_state :=
  (list (list (name × expr × expr)) × nat)

@[reducible] meta def anf_monad :=
  state anf_state

private meta def let_bind (n : name) (ty : expr) (e : expr) : anf_monad unit := do
  scopes <- state.read,
  match scopes with
  | ([], _) := return ()
  | ((s :: ss), count) := state.write $ (((n, ty, e) :: s) :: ss, count)
  end

private meta def is_cases_on (head : expr) : bool :=
  match native.is_internal_cases head with
  | option.some _ := bool.tt
  | option.none :=
    match native.get_builtin (expr.const_name head) with
    | option.some b :=
      match b with
      | builtin.cases _ _ := bool.tt
      | _ := bool.ff
      end
    | option.none := bool.ff
    end
  end

private meta def enter_scope {A} (action : anf_monad A) : anf_monad A := do
  (scopes, count) <- state.read,
  state.write ([] :: scopes, count),
  result <- action,
  state.write (scopes, count),
  return result

private meta def fresh_name : anf_monad name := do
  (ss, count) <- state.read,
  -- need to replace this with unique prefix as per our earlier conversation
  n <- pure $ name.mk_numeral (unsigned.of_nat count) `_anf_,
  state.write (ss, count + 1),
  return n

private meta def mk_neutral_expr : expr :=
  expr.const `_neutral_ []

check @monad.forM

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

private meta def mk_call : expr → list expr → expr
| head [] := head
| head (e :: es) := mk_call (expr.app head e) es

private meta def anf_call (head : expr) (args : list expr) (anf : expr -> anf_monad expr) : anf_monad expr := do
  hoist anf (fun ns, match ns with
  -- need to think about how to refactor this, we should get at least one back from here always
  -- this case should never happen
  | [] := return head
  | (head' :: args') := return $ mk_call head args
  end) args

private meta def anf' : expr -> anf_monad expr
| (expr.elet n ty val body) := do
  let_bind n ty val,
  anf' body
| (expr.app f arg) :=
  let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
   in if is_cases_on fn
      then return (expr.app f arg)
      else anf_call fn args anf'
| e := return e

meta def init_state : anf_state :=
  ([], 0)

meta def anf (e : expr) : expr :=
  trace "anf" (fun u, prod.fst $ (anf' e) init_state)
