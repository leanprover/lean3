/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.meta.format
import init.meta.expr
import init.data.string
import init.category.state

import tools.native.result
import tools.native.internal
import tools.native.builtin

namespace native

meta def is_nat_cases_on (n : name) : bool :=
`nat.cases_on = n

meta def is_cases_on (head : expr) : bool :=
  if is_nat_cases_on (expr.const_name head)
  then bool.tt
  else
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

meta def get_arity : expr → nat
| (expr.lam _ _ _ body) := 1 + get_arity body
| _ := 0

print inductive expr

meta def mk_neutral_expr : expr :=
  expr.const `_neutral_ []


meta definition mk_local (n : name) : expr :=
  expr.local_const n n binder_info.default mk_neutral_expr

meta def mk_call : expr → list expr → expr
| head [] := head
| head (e :: es) := mk_call (expr.app head e) es

-- really need to get out of the meta language so I can prove things, I should just have a unit test lemma
meta def under_lambda' {M} [monad M] (fresh_name : M name) (action : expr -> M expr) : expr → M expr
| (expr.lam n bi ty body) := do
  fresh ← fresh_name,
  body' ← under_lambda' $ expr.instantiate_var body (mk_local fresh),
  return $ expr.lam n bi ty (expr.abstract_local body' fresh)
| e := action e

meta def under_lambda {M} [monad M] (fresh_name : M name) (action : expr -> M expr) (e : expr) : M expr :=
  under_lambda' fresh_name action e

meta def is_return (n : name) : bool :=
  decidable.to_bool $ `native_compiler.return = n

meta def is_assign (n : name) : bool :=
  decidable.to_bool $ `native_compiler.assign = n

inductive application_kind
| cases
| nat_cases
| assign
| constructor : nat -> application_kind
| projection : nat -> application_kind
| return
| other

-- I like this pattern of hiding the annoying C++ interfaces
-- behind more typical FP constructs so we can do case analysis instead.
meta def app_kind (head : expr) : application_kind :=
  -- We need to be careful here, if we want to distinguish cases on
  -- not sure if we should? need to think about it.
  if (expr.is_constant head) && (is_return (expr.const_name head))
  then application_kind.return
  else if (expr.is_constant head) && (is_nat_cases_on (expr.const_name head))
  then application_kind.nat_cases
  else if (expr.is_constant head) && (is_assign (expr.const_name head))
  then application_kind.assign
  else if is_cases_on head
  then application_kind.cases
  else match native.is_internal_cnstr head with
    | some n := application_kind.constructor (unsigned.to_nat n)
    | none := match native.is_internal_proj head with
      | some n := application_kind.projection (unsigned.to_nat n)
      | none := application_kind.other
    end
  end

end native
