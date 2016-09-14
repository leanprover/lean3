import init.meta.format
import init.meta.expr
import system.IO
import system.result

namespace native

inductive error
| string : string -> error

definition result := system.result error

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
| letb : name -> ir_expr -> ir_stmt -> ir_stmt
| e : ir_expr -> ir_stmt
-- use a list here
| seq : ir_stmt -> ir_stmt -> ir_stmt
| return : ir_expr -> ir_stmt
| nop : ir_stmt

inductive ir_decl
| mk : name -> list ir_ty -> ir_ty -> ir_stmt -> ir_decl

definition mk_error {T} : string -> result T :=
  fun s, system.result.err $ error.string s

definition mk_nat_literal (n : nat) : ir_stmt :=
  ir_stmt.e (ir_expr.lit $ ir_literal.nat n)

definition assert_name : ir_expr → result name
| assert_name (ir_expr.name n) := system.result.ok n
| assert_name e := mk_error "expected name, found: "

check tactic.mk_fresh_name

inductive state (S A : Type) : Type
| run : (S → (S × A)) -> state

definition state.pure {S A} (a : A) : state S A :=
  state.run $ fun s, (s, a)

definition state.map {S A B} (f : A → B) : state S A → state S B
| (state.run action) :=
  state.run $ fun s, prod.rec_on (action s) (fun s' a, (s', f a))

definition state.bind {S A B} : state S A → (A → state S B) → state S B
| (state.run action) f :=
  state.run $ fun s,
    prod.rec_on (action s)
      (fun s' a, state.rec_on (f a)
        (fun action_b, action_b s'))

attribute [instance]
definition state_functor (S : Type) : functor (state S) :=
  functor.mk (@state.map S)

attribute [instance]
definition state_monad (S : Type) : monad (state S) :=
  monad.mk (@state.map S) (@state.pure S) (@state.bind S)

structure anf_state :=
  (counter : nat)
  (bindings : list (name × ir_expr))

definition state.get {S} : state S S :=
  state.run $ fun s, (s, s)

definition state.set {S} (new : S) : state S unit :=
  state.run $ fun s', (new, ())

definition update {S} (s : S) (f : S -> S): state S unit := do
  s <- state.get,
  state.set (f s)

-- structure has_field (n : name) (Self : Type) (FieldTy : Type) : Type :=
--   (project : Self → FieldTy)
-- definition name [hf: has_field `name T U] (t : T) : U := hf.project t

definition fresh_name : state anf_state name :=
  sorry

definition let_bind (n : name) (v : expr) : state anf_state unit := do

meta_definition anf_expr' (e : expr) : state anf_state expr :=
  sorry

meta_definition anf_expr (e : expr) (bs : list (name × ir_expr)): ir_expr :=
  match e with
  | expr.app _ _ :=
    let head := expr.app_fn e,
        args := expr.get_app_args e in
    
-- code looks bad, weird monad errors again, there are some issues because I'm still using the old
-- higher order unification based elab, which creates fucking insance solutions
definition mk_call (head : name) (args : list ir_expr) : result ir_expr :=
  let args'' : list (result name) := list.map assert_name args in
  do (args' : list name) <- @monad.sequence result _ _ args'', result.ok $ ir_expr.call head args'

meta_definition is_return (n : name) : bool :=
  decidable.to_bool $ `native_compiler.return = n

meta_definition is_constructor (n : name) : bool :=
  decidable.to_bool $ (mk_num_name (mk_simple_name "_cnstr") 0) = n

meta_definition compile_expr_to_ir_expr (e : expr) : result ir_expr :=
  match e with
   | expr.const n _ :=
     if is_constructor n = bool.tt
     -- TODO should probably restrict the space of nats
     then (pure $ ir_expr.mk_object 0 [])
     else mk_error (name.to_string n)
   | expr.var i := mk_error "found var"
   | expr.sort _ := mk_error "found sort"
   | expr.meta _ _ := mk_error "found meta"
   | expr.local_const _ _ _ _ := mk_error "found local const"
   | expr.app f x :=
      let head := expr.const_name $ expr.app_fn (expr.app f x) in
      let args := expr.get_app_args (expr.app f x) in do
      args' <- @monad.sequence result _ _ $ list.map compile_expr_to_ir_expr args,
      mk_call head args'
   | expr.lam _ _ _ _ := mk_error "found lam"
   | expr.pi _ _ _ _ := mk_error "found pi"
   | expr.elet n _ v body := mk_error "internal error: can not translate let binding into a ir_expr"
   | expr.macro _ _ _ := mk_call (mk_simple_name "macro") []
   end

meta_definition one_or_error (args : list expr) : result expr :=
  match args with
  | ((h : expr) :: []) := system.result.ok h
  | _ := mk_error "internal invariant violated, should only have one argument"
  end

meta_definition compile_app_expr_to_ir_stmt (head : name) (args : list expr) : result ir_stmt :=
  if is_return head = bool.tt
  then do rexp <- one_or_error args, ir_stmt.return <$> compile_expr_to_ir_expr rexp
  else mk_error "can only compile return in head position"

meta_definition compile_expr_to_ir_stmt (e : expr) : result ir_stmt :=
  match e with
  | expr.var i := system.result.ok $ mk_nat_literal (unsigned.to_nat i)
  | expr.sort _ := mk_error "found sort"
  | expr.const n _ := mk_error "found const"
  | expr.meta _ _ := mk_error "found meta"
  | expr.local_const _ _ _ _ := mk_error "found local const"
  | expr.app f x :=
    let head := expr.app_fn (expr.app f x) in
    let args := expr.get_app_args (expr.app f x) in
    if expr.is_constant f = bool.tt
    then compile_app_expr_to_ir_stmt (expr.const_name f) args
    else mk_error "unexpected expr in head position"
  | expr.lam _ _ _ _ := mk_error "found lam"
  | expr.pi _ _ _ _ := mk_error "found pi"
  | expr.elet n _ v body := ir_stmt.letb n <$> compile_expr_to_ir_expr v <*> compile_expr_to_ir_stmt v
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

meta_definition mangle_name (n : name) : format :=
to_fmt $ name.to_string_with_sep "_" n

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
| (ir_stmt.letb n v body) :=
  to_fmt "lean::vm_obj" ++ (mangle_name n) ++ (to_fmt " = ") ++ (format_ir_expr v) ++ to_fmt ";" ++
  format.line ++ format_ir_stmt body
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
    (format_ir_ty ret_ty) ++ format.space ++ (mangle_name n) ++
    (format_argument_list arg_tys) ++ format.space ++
    (format.bracket "{" "}" $ format.line ++ (format.nest 4 body) ++ format.line)
  end

definition unwrap_or_else : Π {T E : Type}, result T → (T → E) → (error -> E) -> E
| T E (result.err e) f err := err e
| T E (result.ok t) f err := f t

-- TODO: fix naming here
meta_definition take_arguments' (e : expr) (ns : list name) : (list name × expr) :=
  match e with
  | (expr.lam n _ _ body) :=  take_arguments' body (n :: ns)
  | e' := ([], e')
  end

meta_definition take_arguments (e : expr) : (list name × expr) :=
  let res := take_arguments' e []
  in (list.reverse (prod.pr1 res), prod.pr2 res)

meta_definition compile_decl (decl_name : name) (e : expr) : format :=
  let arity := get_arity e in
  let args_and_body := take_arguments e in
  let ir := compile_decl_to_ir decl_name arity (prod.pr2 args_and_body) in
  unwrap_or_else ir format_ir (fun e, error.cases_on e (fun s, format.of_string s))

end native
