/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.name
import init.meta.rb_map

namespace ir

inductive base_type
-- primitive unsigned integer types
| u8
| u16
| u32
| u64
| unsigned -- should we have these?
-- primitive signed integer types
| i8
| i16
| i32
| i64
| int -- should we have these?
-- primitive string literals aka `const * char`
| str
-- an unbounded integer
| integer

inductive ty
| base : base_type -> ty
| object : option ty -> ty
| ref : ty → ty
| mut_ref : ty → ty
-- these are temporary
| int : ty
| object_buffer : ty
| name : name → ty

instance : has_coe base_type ty :=
 ⟨ fun bt, ty.base bt ⟩

inductive literal
| nat : nat → literal
| string : string → literal

-- inductive value : Type
-- | name : name → value
-- | lit : literal → value

-- TODO: eventually m
-- odel ty.object, mk_object, project, etc in the IR itself
inductive expr : Type
| call : name → list name → expr
| global : name → expr
| lit : literal → expr
| mk_object : nat → list name → expr
| locl : name → expr
| project : name → nat → expr
| panic : string → expr
| mk_native_closure : name → nat → list name → expr
| invoke : name → list name → expr
| uninitialized : expr
| constructor : name → list name → expr
| address_of : name → expr
-- hack for now, do in secon pass clean up
| equals : expr → expr → expr
| sub : expr → expr → expr
| raw_int : nat → expr
-- | value : value → expr

inductive stmt : Type
| ite : name → stmt → stmt → stmt
| switch : name → list (nat × stmt) → stmt → stmt
| letb : name → ty → expr → stmt → stmt
| e : expr → stmt
| seq : list stmt → stmt
| assign : name → expr → stmt
| return : expr → stmt
| nop : stmt

inductive defn
| mk : name → list (name × ty) → ty → stmt → defn

def defn.to_string : defn → string
| _ := "defn"

instance defn_has_to_string : has_to_string defn :=
  ⟨ defn.to_string ⟩

inductive decl
| mk : name → list (name × ty) → ty → decl

def decl.to_string : decl → string
| _ := "decl"

instance decl_has_to_string : has_to_string decl :=
 ⟨ decl.to_string ⟩

inductive item
| defn : defn → item
| decl : decl → item

def item.get_name : item → name
| (item.defn (defn.mk n _ _ _)) := n
| (item.decl (decl.mk n _ _)) := n

def item.to_string : item → string
| _ := "an item"

instance : has_to_string item :=
 ⟨ item.to_string ⟩

meta record context :=
  (items : rb_map name ir.item)

meta def new_context (decls : list ir.decl) (defns : list ir.defn) : context := do
  let items := list.map (ir.item.defn) defns ++ list.map (ir.item.decl) decls,
  named_items := list.map (fun i, (ir.item.get_name i, i)) $ items in
  context.mk $ rb_map.of_list named_items

meta def lookup_item (n : name) (ctxt : context) : option ir.item :=
  none

end ir

-- def map (K V : Type) : Type :=
--   list (K × V)

-- def lookup {K V} (key : K) (map : map K V) : option V :=
--   sorry

-- def context :=
--   map name ir_decl

-- inductive value
-- | int : nat → value

-- def local_context :=
--   map name ir_expr

-- def call_fn (ctxt : context) (local_cx : local_context) (fn_name : name) (args : list name) : option ir_expr :=
--   sorry

-- -- We fix the global context during evaluation.
-- inductive step_expr (ctxt : context) : local_context → ir_expr → value → Prop
-- | call :
--   forall n args local_cx retval,
--    call_fn ctxt local_cx n args = option.some retval →
--    step_expr local_cx (ir_expr.call n args) retval
-- | local_name :
--   forall n e local_cx retval,
--     lookup n local_cx = option.some e →
--     step_expr local_cx n e

-- inductive step_stmt : context → local_context → ir_stmt → ir_stmt → Prop
-- | nop : forall ctxt local_ctxt,
--   step_stmt ctxt local_ctxt nop nop
-- |
