/-
Copyright (c) 2017 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

namespace ir

inductive symbol
-- A normal hierarchial name.
| name : name → symbol
-- An external name potentially in a namespace.
| external : option name → name → symbol

meta instance : decidable_eq symbol :=
by tactic.mk_dec_eq_instance

instance : has_coe string symbol :=
⟨ fun n, symbol.name n ⟩

instance has_coe_name_symbol : has_coe name symbol :=
⟨ fun n, symbol.name n ⟩

def symbol.to_string : symbol → string
| (symbol.name n) := to_string n
| (symbol.external _ _) := "NYI"

instance : has_to_string symbol :=
⟨ symbol.to_string ⟩

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

#check expr

inductive ty : Type
| base : base_type → ty
| object : option ty → ty
| ref : ty → ty
| mut_ref : ty → ty
-- these are temporary
| object_buffer : ty
| symbol : symbol → ty
| name : name → ty
| array : ty → ty
| raw_ptr : ty → ty
-- | abs : list ty \r

instance has_coe_basetype_ty : has_coe base_type ty :=
⟨ fun bt, ty.base bt ⟩

inductive either (A B : Type) : Type
| left : A → either
| right : B → either

inductive literal : Type
-- this case should be removed, nat literals should be elaborated to `mk_vm_nat : { Z | + } → vm_obj`
| nat : nat → literal
| integer : int → literal
| string : string → literal
-- I think these two can be unified
| binary : string → literal
-- This constructor is a hack, there is a bug with
-- the nested inductive compiler.
| symbol : symbol → literal
| array : list literal → literal

inductive op
| equals
| not_equals
| add
| sub
| mul
| div

-- TODO: eventually m
-- odel ty.object, mk_object, project, etc in the IR itself
inductive expr : Type
| global : symbol → expr
| lit : literal → expr
| mk_object : nat → list symbol → expr
| sym : symbol → expr
| project : symbol → nat → expr
| mk_native_closure : symbol → nat → list symbol → expr
| invoke : symbol → list symbol → expr
| uninitialized : expr
| constructor : symbol → list symbol → expr
| address_of : symbol → expr
| binary_operator : op → expr → expr → expr
-- these need to be literal/values/etc
| array : list symbol → expr
| call : symbol → list symbol → expr
-- | value : value → expr

instance literal_to_expr : has_coe literal expr :=
⟨ expr.lit ⟩

inductive stmt : Type
| ite : symbol → stmt → stmt → stmt
| switch : symbol → list (nat × stmt) → stmt → stmt
| letb : symbol → ty → expr → stmt → stmt
| call : option symbol → symbol → list symbol → stmt
| e : expr → stmt
| seq : list stmt → stmt
| assign : symbol → expr → stmt
| panic : string → stmt
| return : expr → stmt
| unreachable : stmt
| nop : stmt

instance expr_to_stmt : has_coe expr stmt :=
⟨ ir.stmt.e ⟩

def is_extern := bool

inductive defn
| mk : is_extern → name → list (name × ty) → ty → stmt → defn

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

inductive type_decl_body
| struct : list (name × ty) → type_decl_body
| for : list name → type_decl_body

inductive type_decl
| mk : name → type_decl_body → type_decl

inductive item
| defn : defn → item
| decl : decl → item
| type : type_decl → item

def item.get_name : item → name
| (item.defn (defn.mk _ n _ _ _)) := n
| (item.decl (decl.mk n _ _)) := n
| (item.type (type_decl.mk n _)) := n

def item.to_string : item → string
| _ := "an item"

instance item_has_to_string : has_to_string item :=
⟨ item.to_string ⟩

end ir
