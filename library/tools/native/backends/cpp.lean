/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.meta.name
import init.meta.format
import init.function

import tools.native.ir
import tools.native.backend
import tools.native.attributes
import tools.native.util

meta def comma_sep (items : list format) : format :=
format.sep_by (format.of_string "," ++ format.space) items

namespace format_cpp

def one_of (c : char) (s : string) : bool := bool.ff

meta def mangle_external_name (n : name) : string :=
  name.to_string_with_sep "_" n

meta def mangle_name (n : name) : string :=
string.replace_char '''  "_$single_quote$_" $ name.to_string_with_sep "$dot$_" n

meta def mangle_symbol : ir.symbol → string
| (ir.symbol.name n) := "_$lean$_" ++ mangle_name n
| (ir.symbol.external opt_ns n) :=
  match opt_ns with
  | some ns := to_string ns ++ "::" ++ mangle_external_name n
  | none := mangle_external_name n
  end

private meta def mk_constructor_args : list ir.symbol → list format
| [] := []
| (n :: ns) := mangle_symbol n :: mk_constructor_args ns

private meta def mk_constructor
  (arity : nat)
  (fs : list ir.symbol) : format :=
  "lean::mk_vm_constructor(" ++ to_fmt arity ++ "," ++
  (format.bracket "{" "}" (comma_sep $ mk_constructor_args fs)) ++ ")"

private meta def mk_call (symbol : ir.symbol) (args : list ir.symbol) : format :=
  mangle_symbol symbol ++ (format.bracket "(" ")" (comma_sep $ list.map (fun arg, mangle_symbol arg) args))

meta def real_concat : list string -> string
| [] := ""
| (s :: ss) := s ++ real_concat ss

meta def binary_array (bs : string) : format :=
let cs := list.map (fun c, "static_cast<char>(" ++ to_string (char.to_nat c) ++ ")") bs.to_list
in format.bracket "{" "}" (string.intercalate ", " cs)

meta def literal : ir.literal → format
| (ir.literal.nat n) := to_fmt "lean::mk_vm_nat(" ++ to_fmt n ++ ")"
| (ir.literal.integer z) := to_string z
| (ir.literal.string s) := to_string s ++ "s"
| (ir.literal.binary b) := binary_array b
| (ir.literal.array ls) := format.bracket "{" "}" (comma_sep (list.map literal ls))
| (ir.literal.symbol n) := mangle_symbol n

meta def format_local (s : ir.symbol) : format :=
mangle_symbol s

meta def string_lit (s : string) : format :=
format.bracket "\"" "\"" (to_fmt s)

meta def block (body : format) : format :=
"{" ++ (format.nest 4 (format.line ++ body)) ++ format.line ++ "}"

meta def binary_op : ir.op → format
| ir.op.equals := " == "
| ir.op.not_equals := " != "
| ir.op.add := " + "
| ir.op.sub := " - "
| ir.op.mul := " * "
| ir.op.div := " / "

meta def expr' : ir.expr → format
| (ir.expr.mk_object n fs) :=
  if (list.length fs) = 0 /\ n = 0
  -- Over time I should remove these special case functions,
  -- and just use the def language of the IR.
  then to_fmt "lean::mk_vm_simple(0)"
  else
  mk_constructor n fs
| (ir.expr.global n) :=
  mk_call n []
| (ir.expr.sym s) :=
  mangle_symbol s
| (ir.expr.lit l) :=
   literal l
-- project really should only work for like fields/primtive arrays, this is a temporary hack
| (ir.expr.project obj n) :=
  "cfield(" ++ (mangle_symbol obj) ++ ", " ++ (to_fmt n) ++ ")"
| (ir.expr.mk_native_closure n arity args) :=
   if arity < 9
   then "lean::mk_native_closure(" ++ mangle_symbol n ++ ", " ++ format.bracket "{" "}" (comma_sep (list.map format_local args)) ++ ")"
   else "lean::mk_native_closure(" ++ mangle_symbol n ++ ", " ++ arity ++ ", " ++ format.bracket "{" "}" (comma_sep (list.map format_local args)) ++ ")"
| (ir.expr.invoke s args) :=
 "lean::invoke(" ++ mangle_symbol s ++ ", " ++
 (comma_sep (list.map format_local args)) ++ ")"
| (ir.expr.uninitialized) := format.nil
| (ir.expr.constructor _ _) := "NYIctor"
| (ir.expr.address_of e) := "& " ++ mangle_symbol e ++ ";"
| (ir.expr.binary_operator op e1 e2) := expr' e1 ++ binary_op op ++ expr' e2
| (ir.expr.array ns) :=
    format.bracket "{" "}" (comma_sep (list.map format_local ns))
| (ir.expr.call (ir.symbol.name `index) (buf :: index :: _)) :=
  mangle_symbol buf ++ "[" ++ mangle_symbol index ++ "]"
| (ir.expr.call f xs) := mk_call f xs

meta def default_case (body : format) : format :=
to_fmt "default: " ++ block body

meta def insert_newlines (newlines : nat) (fs : list format) : format :=
format.join $ list.intersperse (format.join $ list.repeat format.line newlines) fs

meta def format_lines (fs : list format) : format :=
insert_newlines 1 fs

meta def case (action : ir.stmt → format) : (nat × ir.stmt) → format
| (n, s) := "case " ++ to_fmt n ++ ": " ++ block (action s ++ format.line ++ "break;")

meta def cases (action : ir.stmt → format) (cs : list (nat × ir.stmt)) : format :=
  format_lines (list.map (case action) cs)

meta def base_type : ir.base_type -> format
| ir.base_type.str := "std::string"
| ir.base_type.binary := "char[] "
| ir.base_type.u8 := "NYI"
| ir.base_type.u16 := "NYI"
| ir.base_type.u32 := "NYI"
| ir.base_type.u64 := "NYI"
| ir.base_type.unsigned := "unsigned"
| ir.base_type.i8 := "NYI"
| ir.base_type.i16 := "NYI"
| ir.base_type.i32 := "NYI"
| ir.base_type.i64 := "NYI"
| ir.base_type.int := "int"
| ir.base_type.integer := "lean::mpz"

meta def ty : ir.ty → format
| (ir.ty.object _) := format.of_string "lean::vm_obj"
| (ir.ty.ref T) := ty T ++ format.of_string " const &"
| (ir.ty.mut_ref T) := ty T ++ format.of_string " &"
| (ir.ty.object_buffer) := "lean::buffer<lean::vm_obj>"
| (ir.ty.name n) := to_fmt n ++ format.space
| (ir.ty.base bt) := base_type bt
| (ir.ty.array T) := ty T ++ "[]"
| (ir.ty.symbol s) := mangle_symbol s
| (ir.ty.raw_ptr T) := "const " ++ ty T ++ "*"

meta def parens (inner : format) : format :=
format.bracket "(" ")" inner

meta def stmt_fuse_list : list ir.stmt -> list ir.stmt
| [] := []
| (ir.stmt.letb n ty val ir.stmt.nop :: ir.stmt.assign n' exp :: rest) :=
  if n = n'
  then ir.stmt.letb n ty val (ir.stmt.e exp) :: stmt_fuse_list rest
  else ir.stmt.letb n ty val ir.stmt.nop :: ir.stmt.assign n' exp :: stmt_fuse_list rest
| (s :: ss) := s :: stmt_fuse_list ss

-- wild card doesn't work here for some reason
meta def stmt_fuse : ir.stmt -> ir.stmt
| (ir.stmt.seq ss) := ir.stmt.seq $ stmt_fuse_list ss
| (ir.stmt.return e) := (ir.stmt.return e)
| (ir.stmt.letb n ty val body) := ir.stmt.letb n ty val body
| (ir.stmt.nop) := ir.stmt.nop
| (ir.stmt.ite c t f) := ir.stmt.ite c t f
| (ir.stmt.assign n v) := ir.stmt.assign n v
| (ir.stmt.e e) := ir.stmt.e e
| (ir.stmt.switch s cs d) := ir.stmt.switch s cs d
| e := e

meta def stmt : ir.stmt → format
| (ir.stmt.call _ (ir.symbol.name `index) (buf :: index :: _)) :=
  mangle_symbol buf ++ "[" ++ mangle_symbol index ++ "]"
| (ir.stmt.call _ f xs) := mk_call f xs
| (ir.stmt.e e) := expr' e ++ ";"
| (ir.stmt.return e) :=
    format.of_string "return"  ++
    format.space ++
    expr' e ++ format.of_string ";"
| (ir.stmt.letb n t ir.expr.uninitialized body) :=
  ty t ++ format.space ++ (mangle_symbol n) ++ to_fmt ";" ++ format.line ++ stmt body
  -- type checking should establish that these two types are equal
| (ir.stmt.letb n t (ir.expr.constructor ty_name args) s) :=
  -- temporary hack, need to think about how to model this better
  if ty_name = ir.symbol.external (some `lean) `name
  then let ctor_args := comma_sep (list.map (string_lit ∘ to_string) args) in
    ty t ++ format.space ++ (mangle_symbol n) ++ " = lean::name({" ++ ctor_args ++ "})" ++ to_fmt ";" ++ format.line ++ stmt s
  else let ctor_args := parens $ comma_sep (list.map (fun arg, mangle_symbol arg) args) in
       ty t ++ format.space ++ (mangle_symbol n) ++ ctor_args ++ to_fmt ";" ++ format.line ++ stmt s
| (ir.stmt.letb n t v body) :=
  match t with
  | (ir.ty.array t) :=
    ty t ++ format.space ++ (mangle_symbol n) ++ "[]" ++ (to_fmt " = ") ++ (expr' v) ++ to_fmt ";" ++
    format.line ++ stmt body
  | _ := ty t ++ format.space ++ (mangle_symbol n) ++ (to_fmt " = ") ++ (expr' v) ++ to_fmt ";" ++
    format.line ++ stmt body
  end
| (ir.stmt.switch scrut cs default) :=
  (to_fmt "switch (") ++ (mangle_symbol scrut) ++ (to_fmt ")") ++
  (block (cases stmt cs ++ format.line ++ default_case (stmt default)))
| ir.stmt.nop := format.nil
| (ir.stmt.ite cond tbranch fbranch) :=
  "if (" ++ mangle_symbol cond ++ ") " ++
    block (stmt tbranch) ++ " else " ++
    block (stmt fbranch)
| (ir.stmt.seq cs) :=
  format_lines (list.map (fun c, stmt c) cs)
| (ir.stmt.assign n val) := mangle_symbol n ++ " = " ++ expr' val ++ ";"
| (ir.stmt.panic err_msg) :=
  to_fmt "throw std::runtime_error(" ++ string_lit err_msg ++ ");"
| ir.stmt.unreachable := "lean_unreachable()"

meta def expr := expr'

meta def format_param (param : name × ir.ty) :=
ty (prod.snd param) ++ format.space ++ mangle_symbol (ir.symbol.name $ prod.fst param)

meta def format_argument_list (tys : list (name × ir.ty)) : format :=
  format.bracket "(" ")" (comma_sep (list.map format_param tys))

meta def external : bool -> format
| bool.tt := "extern \"C\" "
| bool.ff := format.nil

-- meta_def format_prototypes ()
meta def defn (d : ir.defn) : format :=
  match d with
  | ir.defn.mk extern n arg_tys ret_ty body :=
    let body' := stmt body,
        nm := if n = "main" then to_fmt (mangle_name n) else (mangle_symbol (ir.symbol.name n))
    in
    external extern ++
    (ty ret_ty) ++ format.space ++ nm ++
    (format_argument_list arg_tys) ++ format.space ++
    block body'
  end

meta def headers : format :=
  format_lines [
    "#include <iostream>",
    "#include <string>",
    "#include \"util/numerics/mpz.h\"",
    "#include \"library/vm/vm_io.h\"",
    "#include \"library/vm/vm.h\"",
    "#include \"library/io_state.h\"",
    "#include \"init/init.h\"",
    "#include \"library/vm/vm_native.h\"",
    "#include \"library/vm/vm_string.h\"",
    "using namespace std::string_literals;",
    -- pretty sure I can remove this
    "static lean::environment * _$lean$_g_env = nullptr;"
  ]

-- todo external symbols should have *no* mangling applied
meta def prototype : ir.defn → format
| (ir.defn.mk extern n params ret_ty _) :=
  external extern ++ ty ret_ty ++ " " ++ mangle_symbol (ir.symbol.name n) ++ format_argument_list params ++ ";" ++ format.line

meta def defn_prototypes (defs : list ir.defn) : format :=
  format.join $ list.map prototype defs

meta def split_items : list ir.item → (list ir.defn × list ir.decl × list ir.type_decl)
| [] := ([], [], [])
| (i :: is) :=
  let (defs, decls, types) := split_items is in
  match i with
  | ir.item.defn d := (d :: defs, decls, types)
  | ir.item.decl d := (defs, d :: decls, types)
  | ir.item.type td := (defs, decls, td :: types)
  end

meta def declaration : ir.decl → format
| (ir.decl.mk n params ret_ty) :=
-- fix the symbol/name situation for decls/defns
  ty ret_ty ++ " " ++ name.to_string_with_sep "_" n ++ format_argument_list params ++ ";"

meta def declarations (decls : list ir.decl) : format :=
  "namespace lean" ++ format.space ++ block (format_lines (list.map declaration decls))

meta def definitions (defs : list ir.defn) : format :=
  insert_newlines 2 $ list.map defn defs

meta def program (items : list ir.item) : format :=
  let (defs, decls, types) := split_items items in
  format_lines [
    headers,
    defn_prototypes defs,
    declarations decls,
    definitions defs
  ]

end format_cpp

namespace native.backend.cpp

open native

meta def add_shared_dependencies (cc : cpp_compiler) : cpp_compiler :=
{ cc with link := cc.link ++ ["gmp", "pthread", "mpfr", "leanshared"].to_buffer }

-- We still have hardwired support for this right now, the eventual goal is to extend the
-- backend interface to have everything needed.
--
-- TODO(@jroesch), move emit_main code here.
meta def write_and_compile [io.interface] (cfg : config) (path : string) (data : buffer char) : io unit :=
do handle ← io.mk_file_handle path io.mode.write,
   io.fs.write handle data,
   io.fs.close handle,
   let cpp := { add_shared_dependencies $ cpp_compiler.mk_executable cfg with files := [path].to_buffer },
   cpp_compiler.run cpp,
   return ()

meta def run_cpp_backend (cfg : config) (ctxt : ir.context) : tactic format :=
do opts ← tactic.get_options,
   let fmt := format_cpp.program $ ctxt.to_items,
   tactic.run_io (fun ioi, @write_and_compile ioi cfg "out.cpp" (fmt.to_buffer opts)),
   return fmt

meta def cpp_compiler (ctxt : ir.context) : tactic unit :=
do cfg ← load_config,
   run_cpp_backend cfg ctxt,
   return ()

@[backend] meta def native.cpp_backend : native.backend :=
{ name := "c++",
  compiler := cpp_compiler }

end native.backend.cpp
