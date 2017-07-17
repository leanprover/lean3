/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import tools.native.ir.util
import tools.native.config
import tools.native.ir.context
import system.except

namespace native

inductive error : Type
| string : string → error
-- | ice : string → error
| many : list error → error

meta def error.to_string : error → string
| (error.string s) := s
| (error.many es) := to_string $ list.map error.to_string es

meta instance error.has_to_string : has_to_string error :=
⟨ λ e, e.to_string ⟩

meta def error.to_format : error → format
| (error.string s) := to_fmt s
| (error.many es) := format.join (es.map error.to_format)

meta instance error.has_to_format : has_to_format error :=
⟨ λ e, e.to_format ⟩

@[reducible] meta def arity_map : Type :=
  rb_map name nat

@[reducible] def ir.result (A : Type) :=
  except error A

meta def mk_arity_map : list (name × expr) → arity_map
| [] := rb_map.mk name nat
| ((n, body) :: rest) := rb_map.insert (mk_arity_map rest) n (get_arity body)

@[reducible] meta def ir_compiler_state :=
  (ir.context × config × arity_map × nat)

-- there is a strange bug here with eta-equiv
@[reducible] meta def ir_compiler : Type → Type :=
  except_t (state ir_compiler_state) error

meta def ir_compiler.or_else (α : Type) : ir_compiler α → ir_compiler α → ir_compiler α :=
fun a1 a2 s,
  let (r, s') := a1 s in
  match r with
  | (except.error e) := a2 s
  | (except.ok a) := (return a, s')
  end

-- meta instance : alternative ir_compiler :=
-- { failure := fun A s, (except.error $ error.string "reached a call to alternative.failure", s),
--   orelse := ir_compiler.or_else,
--   id_map := sorry,
--   pure := sorry,
--   seq := sorry,
--   pure_seq_eq_map := sorry,
--   map_pure := sorry,
--   seq_pure := sorry,
--   seq_assoc := sorry
-- }

meta def lift_state {A} (action : state ir_compiler_state A) : ir_compiler A :=
fun s, let (a, s') := action s in (except.ok a, s')

meta def lift_result {A} (action : ir.result A) : ir_compiler A :=
λ s, (action, s)

meta def configuration : ir_compiler config := do
  (_, config, _, _) <- lift_state $ state.read,
  return config

meta def arities : ir_compiler arity_map := do
  (_, _, map, _) <- lift_state $ state.read,
  return map

meta def get_context : ir_compiler ir.context :=
do (ctxt, _) ← lift_state $ state.read,
    return ctxt

meta def modify (proj : ir_compiler_state → ir_compiler_state) : ir_compiler unit := do
  st <- lift_state $ state.read,
  lift_state $ state.write (proj st)

meta def trace_ir (s : string) : ir_compiler unit :=
do conf ← configuration,
   if config.debug conf
   then trace s (return ())
   else return ()

meta def ir_compiler.run {α : Type} (action : ir_compiler α) (inital : ir_compiler_state): except error α :=
prod.fst $ action inital

-- An `exotic` monad combinator that accumulates errors.
meta def sequence_err : list (ir_compiler ir.item) → ir_compiler (list ir.item × list error)
| [] := return ([], [])
| (action :: remaining) := λ s,
match sequence_err remaining s with
| (except.error e, s') := (except.error e, s)
| (except.ok (res, errs), s') :=
  match action s' with
  | (except.error e, s'') := (except.ok (res, e :: errs), s'')
  | (except.ok v, s'') := (except.ok (v :: res, errs), s'')
  end
end

meta def fresh_name : ir_compiler name :=
do (ctxt, conf, map, counter) ← lift_state state.read,
let fresh := name.mk_numeral (unsigned.of_nat counter) `native._ir_compiler_,
lift_state $ state.write (ctxt, conf, map, counter + 1),
return fresh

end native
