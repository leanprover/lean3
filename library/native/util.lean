import init.meta.format
import init.meta.expr
import init.string
import system.IO
import system.result
import init.state
import native.internal
import native.builtin

meta def is_cases_on (head : expr) : bool :=
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

meta definition mk_local (n : name) : expr :=
  expr.local_const n n binder_info.default (expr.const n [])

meta def mk_neutral_expr : expr :=
  expr.const `_neutral_ []

meta def mk_call : expr → list expr → expr
| head [] := head
| head (e :: es) := mk_call (expr.app head e) es

meta def under_lambda {M} [monad M] (action : expr -> M expr) : expr → M expr
| (expr.lam n bi ty body) := do
  body' <- action $ expr.instantiate_var body (mk_local n),
  return $ expr.lam n bi ty (expr.abstract body (mk_local n))
| e := action e

inductive application_kind
| cases
| constructor
| other

-- I like this pattern of hiding the annoying C++ interfaces
-- behind more typical FP constructs so we can do case analysis instead.
meta def app_kind (head : expr) : application_kind :=
if is_cases_on head
then application_kind.cases
else match native.is_internal_cnstr head with
| some _ := application_kind.constructor
| none := application_kind.other
end
