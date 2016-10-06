import init.meta.format
import native.ir

definition intersperse {A : Type} (elem : A) : list A -> list A
| [] := []
| (x :: []) := [x]
| (x :: xs) := x :: elem :: intersperse xs

meta definition format_concat : list format → format
| [] := format.nil
| (f :: fs) := f ++ format_concat fs

meta definition comma_sep (items : list format) : format :=
format_concat
  (intersperse (format.of_string "," ++ format.space) items)

namespace format_cpp

meta definition mangle_name (n : name) : format :=
to_fmt $ name.to_string_with_sep "_" n

private meta definition mk_constructor_args : list name → list format
| [] := []
| (n :: ns) := mangle_name n :: mk_constructor_args ns

private meta definition mk_constructor
  (arity : nat)
  (fs : list name) : format :=
  "lean::mk_vm_constructor(" ++ to_fmt arity ++ "," ++
  (format.bracket "{" "}" (comma_sep $ mk_constructor_args fs)) ++ ")"

private meta definition mk_call (symbol : name) (args : list name) : format :=
  mangle_name symbol ++ (format.bracket "(" ")" (comma_sep $ list.map mangle_name args))

meta definition literal : ir.literal → format
| (ir.literal.nat n) := to_fmt "lean::mk_vm_nat(" ++ to_fmt n ++ ")"

meta def format_local (n : name) : format :=
  to_fmt (name.to_string_with_sep "_" n)

meta definition expr' (action : ir.stmt -> format) : ir.expr -> format
| (ir.expr.call f xs) := mk_call f xs
| (ir.expr.mk_object n fs) :=
  if n = 0
  -- Over time I should remove these special case functions,
  -- and just use the definition language of the IR.
  then to_fmt "lean::mk_vm_simple(0)"
  else mk_constructor n fs
| (ir.expr.global n) :=
  mk_call n []
| (ir.expr.locl n) :=
  mangle_name n
| (ir.expr.lit l) :=
   literal l
| (ir.expr.block s) :=
  format.bracket "{" "}" (action s)
| (ir.expr.project obj n) :=
  (mangle_name obj) ++ (format.bracket "[" "]" (to_fmt n))
| (ir.expr.panic err_msg) :=
  to_fmt "throw \"error\""
| (ir.expr.mk_native_closure n args) :=
"lean::mk_native_closure(*g_env, lean::name({\"" ++ name.to_string_with_sep "\", \"" n ++ "\"})" ++ "," ++
   format.bracket "{" "}" (comma_sep (list.map format_local args)) ++ ")"

-- meta def case : 

meta def block (body : format) : format :=
  format.bracket "{" "}" (format.nest 4 (format.line ++ body ++ format.line))

meta def default_case (body : format) : format :=
  to_fmt "default:" ++ block body

meta def stmt : ir.stmt → format
| (ir.stmt.e e) := expr' stmt e
| (ir.stmt.return e) :=
  format.of_string "return"  ++
  format.space ++
  expr' stmt e ++ format.of_string ";"
| (ir.stmt.letb n v body) :=
  to_fmt "lean::vm_obj " ++ (mangle_name n) ++ (to_fmt " = ") ++ (expr' stmt v) ++ to_fmt ";" ++
  format.line ++ stmt body
| (ir.stmt.switch _ _ _) := format.of_string "a"

  -- (to_fmt "switch (cidx(") ++ (mangle_name scrut) ++ (to_fmt "))") ++
  -- (block (to_fmt "cases")) ++
  -- default_case "unreach"

| _ := format.of_string "NYI"

meta def expr := expr' stmt

meta definition ty : ir.ty → format
| ir.ty.object := format.of_string "lean::vm_obj"
| (ir.ty.ref T) := ty T ++ format.of_string " const &"
| (ir.ty.mut_ref T) := ty T ++ format.of_string " &"
| (ir.ty.tag _ _) := format.of_string "an_error"

meta definition format_param (param : name × ir.ty) :=
ty (prod.snd param) ++
format.space ++
to_fmt (name.to_string_with_sep "_" (mk_str_name "_$local$_" (name.to_string_with_sep "_" (prod.fst param))))

meta definition format_argument_list (tys : list (name × ir.ty)) : format :=
  format.bracket "(" ")" (comma_sep (list.map format_param tys))

-- meta_definition format_prototypes ()
meta definition decl (d : ir.decl) : format :=
  match d with
  | ir.decl.mk n arg_tys ret_ty body :=
    let body := stmt body in
    (ty ret_ty) ++ format.space ++ (mangle_name n) ++
    (format_argument_list arg_tys) ++ format.space ++
    (format.bracket "{" "}" $ format.nest 4 (format.line ++ body) ++ format.line)
  end

end format_cpp
