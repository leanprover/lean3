/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.name
import init.meta.rb_map
import init.meta.mk_dec_eq_instance

namespace ir

inductive symbol
-- A normal hierarchial name.
| name : name -> symbol
-- An external name potentially in a namespace.
| external : option name -> name -> symbol

meta instance : decidable_eq symbol :=
  by tactic.mk_dec_eq_instance

instance : has_coe string symbol :=
(| fun n, symbol.name n |)

instance has_coe_name_symbol : has_coe name symbol :=
(| fun n, symbol.name n |)

def symbol.to_string : symbol -> string
| (symbol.name n) := to_string n
| (symbol.external _ _) := "NYI"

instance : has_to_string symbol :=
(| symbol.to_string |)

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
| binary
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
| symbol : symbol -> ty
| name : name → ty
| array : ty -> ty
| raw_ptr : ty -> ty

-- bug here if you omit name
instance has_coe_basetype_ty : has_coe base_type ty :=
 ⟨ fun bt, ty.base bt ⟩

inductive literal
| nat : nat → literal
| string : string → literal
-- I think these two can be unified
| binary : string → literal
| array : list literal -> literal

-- inductive value : Type
-- | name : name → value
-- | lit : literal → value

-- TODO: eventually m
-- odel ty.object, mk_object, project, etc in the IR itself
inductive expr : Type
| call : symbol → list symbol → expr
| global : symbol → expr
| lit : literal → expr
| mk_object : nat → list symbol → expr
| sym : symbol → expr
| project : symbol → nat → expr
| panic : string → expr
| mk_native_closure : symbol → nat → list symbol → expr
| invoke : symbol → list symbol → expr
| uninitialized : expr
| constructor : symbol → list symbol → expr
| address_of : symbol → expr
-- hack for now, do in secon pass clean up
| equals : expr → expr → expr
| sub : expr → expr → expr
| raw_int : nat → expr
| unreachable : expr
| array : list symbol -> expr
-- | value : value → expr

inductive stmt : Type
| ite : symbol → stmt → stmt → stmt
| switch : symbol → list (nat × stmt) → stmt → stmt
| letb : symbol → ty → expr → stmt → stmt
| e : expr → stmt
| seq : list stmt → stmt
| assign : symbol → expr → stmt
| return : expr → stmt
| nop : stmt

def is_extern := bool

inductive defn
| mk : is_extern -> name → list (name × ty) → ty → stmt → defn

def defn.to_string : defn → string
| (defn.mk _ n ps ret body) := "def " ++ to_string n ++ "..."

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
| (item.defn (defn.mk _ n _ _ _)) := n
| (item.decl (decl.mk n _ _)) := n

def item.to_string : item → string
| _ := "an item"

instance item_has_to_string : has_to_string item :=
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
