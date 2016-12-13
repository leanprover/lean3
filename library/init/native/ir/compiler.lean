/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.format
import init.meta.expr
import init.category.state
import init.data.string
import init.data.list.instances

import init.native.util
import init.native.config
import init.native.result
import init.native.ir.context

namespace native

inductive error
| string : string → error
| many : list error → error

meta def error.to_string : error → string
| (error.string s) := s
| (error.many es) := to_string $ list.map error.to_string es

@[reducible] meta def arity_map : Type :=
  rb_map name nat

@[reducible] def ir.result (A : Type) :=
  result error A

meta def mk_arity_map : list (name × expr) → arity_map
| [] := rb_map.mk name nat
| ((n, body) :: rest) := rb_map.insert (mk_arity_map rest) n (get_arity body)

@[reducible] meta def ir_compiler_state :=
  (ir.context × config × arity_map × nat)

@[reducible] meta def ir_compiler (A : Type) :=
  resultT (state ir_compiler_state) error A

meta def lift {A} (action : state ir_compiler_state A) : ir_compiler A :=
  ⟨fmap (fun (a : A), native.result.ok a) action⟩

meta def configuration : ir_compiler config := do
  (_, config, _, _) <- lift $ state.read,
  return config

meta def arities : ir_compiler arity_map := do
  (_, _, map, _) <- lift $ state.read,
  return map

meta def get_context : ir_compiler ir.context := do
  (ctxt, _) <- lift $ state.read,
  return ctxt

meta def modify (proj : ir_compiler_state → ir_compiler_state) : ir_compiler unit := do
  st <- lift $ state.read,
  lift $ state.write (proj st)

-- meta def name_counter : ir_compiler config := do
--   (_, _, counter, _) ← lift $ state.read,
--   return counter

end native
