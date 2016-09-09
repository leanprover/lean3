import init.meta.format
import init.meta.expr
import system.IO

namespace native

set_option new_elaborator true

inductive error
| mk

inductive result : Type -> Type
| err : Π {T}, error -> result T
| ok : Π {T}, T -> result T

definition unwrap_or {T : Type} : result T -> T -> T
| (result.err _) default := default
| (result.ok t) _ := t

definition result_and_then {T U : Type} : result T → (T -> result U) → result U
| (result.err e) _ := result.err e
| (result.ok t) f := f t

-- -- todo impl monad, use monad
-- definition sequence {T : Type} : list (result T) -> result (list T)
-- | [] := result.ok []
-- | (x :: xs) :=
--   result_and_then x (fun t, result_and_then (sequence xs) (fun ts', t :: ts'))

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
| call : name -> ir_expr -> ir_expr
| name : name -> ir_expr
| lit : ir_literal -> ir_expr

inductive ir_stmt : Type
| ite : ir_expr -> ir_stmt -> ir_stmt -> ir_stmt
-- | switch : expr -> list (expr, stmt) -> ir_stmt -> ir_stmt
| letb : name -> ir_stmt -> ir_stmt -> ir_stmt
| e : ir_expr -> ir_stmt
| seq : ir_stmt -> ir_stmt -> ir_stmt
| nop : ir_stmt

-- inductive ir_decl
-- | mk : name -> list ir_ty -> ir_ty -> ir_stmt -> ir_decl

-- definition mk_error {T} : result T :=
--   result.err error.mk

-- definition mk_nat_literal (n : nat) : ir_stmt :=
--   ir_stmt.e (ir_expr.lit $ ir_literal.nat n)

-- meta_definition compile_expr_to_ir (e : expr) : result ir_stmt :=
--   match e with
--   | expr.var i := result.ok $ mk_nat_literal (unsigned.to_nat i)
--   | expr.sort _ := @mk_error ir_stmt
--   | expr.const n _ := mk_error
--   | expr.meta _ _ := mk_error
--   | expr.local_const _ _ _ _ := mk_error
--   | expr.app f x := mk_error
--   | expr.lam _ _ _ _ := mk_error
--   | expr.pi _ _ _ _ := mk_error
--   | expr.elet _ _ _ _ := mk_error
--   | expr.macro _ _ _ := mk_error
--   end

-- meta_definition get_arity (e : expr) : nat :=
-- match e with
-- | expr.lam _ _ _ body := 1 + get_arity body
-- | _ := 0
-- end

-- definition repeat {A : Type} : nat -> A -> list A
-- | repeat 0 _ := []
-- | repeat (n + 1) a := a :: repeat n a

-- meta_definition compile_decl_to_ir (decl_name : name) (arity : nat) (body : expr) : ir_decl := sorry
--   let body' := unwrap_or (compile_expr_to_ir body) ir_stmt.nop in
--   ir_decl.mk decl_name (repeat arity (ir_ty.ref ir_ty.object)) ir_ty.object body'

-- meta_definition format_ir_ty (ty : ir_ty) : format :=
-- match ty with
-- | ir_ty.object := format.of_string "lean::vm_obj"
-- | (ir_ty.ref T) := format_ir_ty T ++ format.of_string " const & "
-- | (ir_ty.mut_ref T) := format_ir_ty T ++ format.of_string " & "
-- | (ir_ty.tag _ _) := format.of_string "an_error"
-- end

-- definition intersperse {A : Type} (elem : A) : list A -> list A
-- | intersperse [] := []
-- | intersperse (x :: xs) :=
--   match xs with
--   | [] := [x]
--   | ys := x :: elem :: intersperse xs
--   end

-- meta_definition format_concat (xs : list format) : format :=
-- match xs with
-- | [] := format.nil
-- | (f :: fs) := f ++ format_concat fs
-- end

-- meta_definition format_argument_list (tys : list ir_ty) : format :=
--   format.bracket "(" ")" (format_concat (intersperse (format.of_string "," ++ format.space) (list.map format_ir_ty tys)))

-- -- meta_definition format_prototypes ()
-- meta_definition format_ir (decl : ir_decl) : format :=
--   match decl with
--   | ir_decl.mk n arg_tys ret_ty stmt :=
--     (format_ir_ty ret_ty) ++ format.space ++ (to_fmt n) ++
--     (format_argument_list arg_tys) ++ format.space ++
--     (format.bracket "{" "}" $ format.nest 4 (format.line ++ format.of_string "ir_stmt" ++ format.line))
--   end

-- meta_definition compile_decl (decl_name : name) (e : expr) : format :=
--   let arity := get_arity e in
--   format_ir (compile_decl_to_ir decl_name arity e)

end native
