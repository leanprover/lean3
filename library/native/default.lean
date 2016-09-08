import init.meta.format
import init.meta.expr
import system.IO

namespace native

inductive tag_ty
| mk

inductive ir_ty
| object : ir_ty
| ref : ir_ty -> ir_ty
| mut_ref : ir_ty -> ir_ty
| tag : tag_ty -> ir_ty -> ir_ty

inductive ir_expr
| call : name -> ir_expr -> ir_expr
| name : name -> ir_expr

inductive ir_stmt : Type
| ite : ir_expr -> ir_stmt -> ir_stmt -> ir_stmt
-- | switch : expr -> list (expr, stmt) -> ir_stmt -> ir_stmt
| letb : name -> ir_stmt -> ir_stmt -> ir_stmt
| e : ir_expr -> ir_stmt
| seq : ir_stmt -> ir_stmt -> ir_stmt
| nop : ir_stmt

inductive ir_decl
| mk : name -> list ir_ty -> ir_ty -> ir_stmt -> ir_decl

definition compile_expr_to_ir (e : expr) : ir_stmt :=
  ir_stmt.nop

meta_definition get_arity (e : expr) : nat :=
match e with
| expr.lam _ _ _ body := 1 + get_arity body
| _ := 0
end

definition repeat {A : Type} : nat -> A -> list A
| repeat 0 _ := []
| repeat (n + 1) a := a :: repeat n a

definition compile_decl_to_ir (decl_name : name) (arity : nat) (body : expr) : ir_decl :=
  ir_decl.mk decl_name (repeat arity (ir_ty.ref ir_ty.object)) ir_ty.object (compile_expr_to_ir body)

meta_definition format_ir_ty (ty : ir_ty) : format :=
match ty with
| ir_ty.object := format.of_string "lean::vm_obj"
| (ir_ty.ref T) := format_ir_ty T ++ format.of_string " const & "
| (ir_ty.mut_ref T) := format_ir_ty T ++ format.of_string " & "
| (ir_ty.tag _ _) := format.of_string "an_error"
end

definition intersperse {A : Type} (elem : A) : list A -> list A
| intersperse [] := []
| intersperse (x :: xs) :=
  match xs with
  | [] := [x]
  | ys := x :: elem :: intersperse xs
  end

definition foo := (intersperse (1 : nat) [1, 2, 3])

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
    (format_ir_ty ret_ty) ++ format.space ++ (to_fmt n) ++
    (format_argument_list arg_tys) ++ format.space ++
    (format.bracket "{" "}" $ format.nest 4 (format.line ++ format.of_string "ir_stmt" ++ format.line))
  end

meta_definition compile_decl (decl_name : name) (e : expr) : format :=
  let arity := get_arity e in
  format_ir (compile_decl_to_ir decl_name arity e)

-- | compile_decl (var index) := format.of_string "var"
-- | compile_decl _ := format.of_string "tool"

end native
