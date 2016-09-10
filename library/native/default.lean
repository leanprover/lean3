import init.meta.format
import init.meta.expr
import system.IO

namespace native

-- set_option new_elaborator true

inductive error
| string : string -> error

inductive result : Type -> Type
| err : Π {T}, error -> result T
| ok : Π {T}, T -> result T

-- TODO: elaborator is still underway, eventually clean these up, hacking around elab bugs
definition unwrap_or : Π {T : Type}, result T -> T -> T
| T (result.err _) default := default
| T (result.ok t) _ := t

definition result.map : Π {T U : Type}, (T → U) → result T → result U
| T U f (result.err e) := result.err e
| T U f (result.ok t) := result.ok (f t)

definition result.and_then : Π {T U : Type}, result T → (T -> result U) → result U
| T U (result.err e) _ := result.err e
| T U (result.ok t) f := f t

attribute [instance]
definition result_functor : functor result :=
{| functor, map := @result.map |}

definition result.seq : Π {T U : Type}, result (T → U) -> result T → result U
| T U f t := result.and_then f (fun f', result.and_then t (fun t', result.ok (f' t')))

attribute [instance]
definition result_applicative : applicative result :=
{| applicative,
   pure := @result.ok,
   map := @result.map,
   seq := @result.seq |}

inductive tag_ty
| mk

inductive ir_ty
| object : ir_ty
| ref : ir_ty -> ir_ty
| mut_ref : ir_ty -> ir_ty
| tag : tag_ty -> ir_ty -> ir_ty

inductive ir_literal
| nat : nat -> ir_literal

inductive ir_expr
| call : name -> list name -> ir_expr
| name : name -> ir_expr
| lit : ir_literal -> ir_expr
| mk_object : nat -> list name -> ir_expr

inductive ir_stmt : Type
| ite : ir_expr -> ir_stmt -> ir_stmt -> ir_stmt
-- | switch : expr -> list (expr, stmt) -> ir_stmt -> ir_stmt
| letb : name -> ir_stmt -> ir_stmt -> ir_stmt
| e : ir_expr -> ir_stmt
-- use a list here
| seq : ir_stmt -> ir_stmt -> ir_stmt
| return : ir_expr -> ir_stmt
| nop : ir_stmt

inductive ir_decl
| mk : name -> list ir_ty -> ir_ty -> ir_stmt -> ir_decl

definition mk_error {T} : string -> result T :=
  fun s, result.err $ error.string s

definition mk_nat_literal (n : nat) : ir_stmt :=
  ir_stmt.e (ir_expr.lit $ ir_literal.nat n)

definition mk_call (head : name) (e : list expr) : result ir_expr :=
  pure $ ir_expr.call head []

meta_definition is_return (n : name) : bool :=
  decidable.to_bool $ `native_compiler.return = n

meta_definition is_constructor (n : name) :=
  decidable.to_bool $ (mk_simple_name "_cnstr.0") = n

meta_definition compile_expr_to_ir_expr (e : expr) : result ir_expr :=
  match e with
  | expr.app f x :=
    let head := expr.app_fn (expr.app f x) in
    let args := expr.get_app_args (expr.app f x) in
    if expr.is_constant f = bool.tt
      then if is_return (expr.const_name f) = bool.tt
        then compile_expr_to_ir_expr x
        else mk_call (expr.const_name head) []
      else mk_error "unexpected expr in head position"
   | expr.const n _ :=
     if is_constructor n = bool.tt
     -- TODO should probably restrict the space of nats
     then (pure $ ir_expr.mk_object 0 [])
     else mk_error (name.to_string n)
   | _ := mk_error "unsupported expr in compile_expr_to_ir_expr"
  end

meta_definition compile_expr_to_ir_stmt (e : expr) : result ir_stmt :=
  match e with
  | expr.var i := result.ok $ mk_nat_literal (unsigned.to_nat i)
  | expr.sort _ := mk_error "found sort"
  | expr.const n _ := mk_error "found const"
  | expr.meta _ _ := mk_error "found meta"
  | expr.local_const _ _ _ _ := mk_error "found local const"
  | expr.app f x := result.map ir_stmt.e $ compile_expr_to_ir_expr (expr.app f x)
  | expr.lam _ _ _ _ := mk_error "found lam"
  | expr.pi _ _ _ _ := mk_error "found pi"
  | expr.elet _ _ _ _ := mk_error "found elet"
  | expr.macro _ _ _ := mk_error "found macro"
  end

meta_definition get_arity (e : expr) : nat :=
  match e with
  | expr.lam _ _ _ body := 1 + get_arity body
  | _ := 0
  end

definition repeat {A : Type} : nat -> A -> list A
| 0 _ := []
| (n + 1) a := a :: repeat n a

meta_definition compile_decl_to_ir (decl_name : name) (arity : nat) (body : expr) : result ir_decl := do
  result.and_then (compile_expr_to_ir_stmt body)
  (fun (body' : ir_stmt), pure (ir_decl.mk decl_name (repeat arity (ir_ty.ref ir_ty.object)) ir_ty.object body'))

meta_definition format_ir_expr (stmt : ir_expr) : format :=
match stmt with
| (ir_expr.call f xs) := to_fmt f
| (ir_expr.mk_object n fs) :=
  if n = 0
  then to_fmt "lean::mk_vm_simple()"
  else to_fmt "error: not ready to make these yet"
| _ := format.of_string "expr NYI"
end

meta_definition format_ir_stmt (stmt : ir_stmt) : format :=
match stmt with
| (ir_stmt.e e) := format_ir_expr e
| (ir_stmt.return e) := format.of_string "return"  ++ format.space ++ format_ir_expr e ++ format.of_string ";"
| _ := format.of_string "NYI"
end

meta_definition format_ir_ty (ty : ir_ty) : format :=
match ty with
| ir_ty.object := format.of_string "lean::vm_obj"
| (ir_ty.ref T) := format_ir_ty T ++ format.of_string " const & "
| (ir_ty.mut_ref T) := format_ir_ty T ++ format.of_string " & "
| (ir_ty.tag _ _) := format.of_string "an_error"
end

definition intersperse {A : Type} (elem : A) : list A -> list A
| intersperse [] := []
| intersperse (x :: []) := [x]
| intersperse (x :: xs) := x :: elem :: intersperse xs

meta_definition format_concat (xs : list format) : format :=
match xs with
| [] := format.nil
| (f :: fs) := f ++ format_concat fs
end

meta_definition format_argument_list (tys : list ir_ty) : format :=
  format.bracket "(" ")" (format_concat (intersperse (format.of_string "," ++ format.space) (list.map format_ir_ty tys)))

-- meta_definition format_prototypes ()
meta_definition format_ir (decl : ir_decl) : format :=
  match decl with
  | ir_decl.mk n arg_tys ret_ty stmt :=
    let body := format_ir_stmt stmt in
    (format_ir_ty ret_ty) ++ format.space ++ (to_fmt n) ++
    (format_argument_list arg_tys) ++ format.space ++
    (format.bracket "{" "}" $ format.line ++ (format.nest 4 body) ++ format.line)
  end

definition unwrap_or_else : Π {T E : Type}, result T → (T → E) → (error -> E) -> E
| T E (result.err e) f err := err e
| T E (result.ok t) f err := f t

meta_definition compile_decl (decl_name : name) (e : expr) : format :=
  let arity := get_arity e in
  let ir := compile_decl_to_ir decl_name arity e in
  unwrap_or_else ir format_ir (fun e, error.cases_on e (fun s, format.of_string s))

end native
