import init.meta.format
import init.meta.expr
import init.string
import system.IO
import system.result
import native.ir

namespace native

inductive error
| string : string -> error

attribute [reducible]
definition result (A : Type*) :=
  system.result error A

definition mk_error {T} : string -> result T :=
  fun s, system.result.err $ error.string s

definition mk_nat_literal (n : nat) : result ir.expr :=
  return (ir.expr.lit $ ir.literal.nat n)

definition assert_name : ir.expr → result name
| (ir.expr.name n) := system.result.ok n
| (ir.expr.call _ _) := mk_error "expected name, found: call "
| (ir.expr.lit _) := mk_error "expected name, found: lit "
| (ir.expr.mk_object _ _) := mk_error "expected name, found: obj "

-- attribute [instance]
-- definition state_functor (S : Type) : functor (state S) :=
--   functor.mk (@state.map S)

-- attribute [instance]
-- definition state_monad (S : Type) : monad (state S) :=
--   monad.mk (@state.map S) (@state.pure S) (@state.bind S)

-- definition fresh_name : state anf_state name :=
--   sorry

-- definition let_bind (n : name) (v : expr) : state anf_state unit := do

-- meta_definition anf_expr' (e : expr) : state anf_state expr :=
--   sorry

-- meta_definition anf_expr (e : expr) (bs : list (name × ir.expr)): ir.expr :=
--   sorry
--   -- match e with
--   -- | expr.app _ _ :=
--   --   let head := expr.app_fn e,
--   --       args := expr.get_app_args e in

-- code looks bad, weird monad errors again, there are some issues because I'm still using the old
-- higher order unification based elab, which creates fucking insance solutions
definition mk_call (head : name) (args : list ir.expr) : result ir.expr :=
  have args'' : list (result name), from list.map assert_name args,
  do (args' : list name) <- @monad.sequence (@@result) _ _ args'',
  system.result.ok $ ir.expr.call head args'

meta_definition is_return (n : name) : bool :=
  decidable.to_bool $ `native_compiler.return = n

meta_definition is_constructor (n : name) : bool :=
  decidable.to_bool $ (mk_num_name (mk_simple_name "_cnstr") 0) = n

-- this code isnt' great working around the semi-functional frontend
meta_definition compile_expr_app_to_ir_expr
  (head : name)
  (args : list expr)
  (action : expr -> result ir.expr) : result ir.expr := do
    args' <- @monad.sequence result _ _ $ list.map action args,
    mk_call head args'

meta_definition compile_expr_macro_to_ir_expr
  (def : macro_def)
  (sz : unsigned)
  (args : fin (unsigned.to_nat sz) -> expr)
  (action : expr → result ir.expr): result ir.expr :=
  if `nat_value_macro = expr.macro_def_name def
  then mk_call (expr.macro_def_name def) [] 
  else mk_call (expr.macro_def_name def) []

meta_definition compile_expr_to_ir_expr : expr → result ir.expr
| (expr.const n _) :=
  if is_constructor n = bool.tt
  -- TODO should probably restrict the space of nats
  then (pure $ ir.expr.mk_object 0 [])
  else mk_error (name.to_string n)
| (expr.var i) := mk_error "there should be no bound variables in compiled terms"
| (expr.sort _) := mk_error "found sort"
| (expr.meta _ _) := mk_error "found meta"
| (expr.local_const _ _ _ _) := mk_error "found local const"
| (expr.app f x) :=
  have head : name, from expr.const_name $ expr.app_fn (expr.app f x),
  have args : list expr, from expr.get_app_args (expr.app f x), do
  compile_expr_app_to_ir_expr head args compile_expr_to_ir_expr
| (expr.lam _ _ _ _) := mk_error "found lam"
| (expr.pi _ _ _ _) := mk_error "found pi"
| (expr.elet n _ v body) := mk_error "internal error: can not translate let binding into a ir_expr"
| (expr.macro def sz args) := compile_expr_macro_to_ir_expr def sz args compile_expr_to_ir_expr

meta_definition one_or_error (args : list expr) : result expr :=
  match args with
  | ((h : expr) :: []) := system.result.ok h
  | _ := mk_error "internal invariant violated, should only have one argument"
  end

meta_definition compile_app_expr_to_ir_stmt (head : name) (args : list expr) : result ir.stmt :=
  if is_return head = bool.tt
  then do rexp <- one_or_error args, ir.stmt.return <$> compile_expr_to_ir_expr rexp
  else mk_error "can only compile return in head position"

meta_definition compile_expr_to_ir_stmt : expr -> result ir.stmt
| (expr.sort _) := mk_error "found sort"
| (expr.const n _) := mk_error "found const"
| (expr.meta _ _) := mk_error "found meta"
| (expr.local_const _ _ _ _) := mk_error "found local const"
| (expr.app f x) :=
  have head : expr, from expr.app_fn (expr.app f x),
  have args : list expr, from expr.get_app_args (expr.app f x),
  if expr.is_constant f = bool.tt
  then compile_app_expr_to_ir_stmt (expr.const_name f) args
  else mk_error "unexpected expr in head position"
| (expr.lam _ _ _ _) := mk_error "found lam"
| (expr.pi _ _ _ _) := mk_error "found pi, should not be translating a Pi for any reason (yet ...)"
| (expr.elet n _ v body) := ir.stmt.letb n <$> compile_expr_to_ir_expr v <*> compile_expr_to_ir_stmt body
| e' := ir.stmt.e <$> compile_expr_to_ir_expr e'

meta_definition get_arity : expr -> nat
| (expr.lam _ _ _ body) := 1 + get_arity body
| _ := 0

definition repeat {A : Type} : nat -> A -> list A
| 0 _ := []
| (n + 1) a := a :: repeat n a

meta_definition compile_decl_to_ir (decl_name : name) (arity : nat) (body : expr) : result ir.decl := do
  system.result.and_then (compile_expr_to_ir_stmt body)
  (fun (body' : ir.stmt), pure (ir.decl.mk decl_name (repeat arity (ir.ty.ref ir.ty.object)) ir.ty.object body'))

meta_definition mangle_name (n : name) : format :=
to_fmt $ name.to_string_with_sep "_" n

meta_definition format_ir_expr : ir.expr -> format
| (ir.expr.call f xs) := to_fmt f
| (ir.expr.mk_object n fs) :=
  if n = 0
  then to_fmt "lean::mk_vm_simple()"
  else to_fmt "error: not ready to make these yet"
| (ir.expr.name n) :=
  mangle_name n
| (ir.expr.lit l) :=
  to_fmt "a lit"

meta_definition format_ir_stmt : ir.stmt → format
| (ir.stmt.e e) := format_ir_expr e
| (ir.stmt.return e) := format.of_string "return"  ++ format.space ++ format_ir_expr e ++ format.of_string ";"
| (ir.stmt.letb n v body) :=
  to_fmt "lean::vm_obj " ++ (mangle_name n) ++ (to_fmt " = ") ++ (format_ir_expr v) ++ to_fmt ";" ++
  format.line ++ format_ir_stmt body
| _ := format.of_string "NYI"

meta_definition format_ir_ty : ir.ty → format
| ir.ty.object := format.of_string "lean::vm_obj"
| (ir.ty.ref T) := format_ir_ty T ++ format.of_string " const & "
| (ir.ty.mut_ref T) := format_ir_ty T ++ format.of_string " & "
| (ir.ty.tag _ _) := format.of_string "an_error"

definition intersperse {A : Type} (elem : A) : list A -> list A
| [] := []
| (x :: []) := [x]
| (x :: xs) := x :: elem :: intersperse xs

meta_definition format_concat : list format → format
| [] := format.nil
| (f :: fs) := f ++ format_concat fs

meta_definition format_argument_list (tys : list ir.ty) : format :=
  format.bracket "(" ")" (format_concat (intersperse (format.of_string "," ++ format.space) (list.map format_ir_ty tys)))

-- meta_definition format_prototypes ()
meta_definition format_ir (decl : ir.decl) : format :=
  match decl with
  | ir.decl.mk n arg_tys ret_ty stmt :=
    have body : format, from format_ir_stmt stmt,
    (format_ir_ty ret_ty) ++ format.space ++ (mangle_name n) ++
    (format_argument_list arg_tys) ++ format.space ++
    (format.bracket "{" "}" $ format.line ++ (format.nest 4 body) ++ format.line)
  end

definition unwrap_or_else {T E : Type} : result T → (T → E) → (error -> E) -> E
| (system.result.err e) f err := err e
| (system.result.ok t) f err := f t

-- TODO: fix naming here
private meta_definition take_arguments' : expr → list name → (list name × expr)
| (expr.lam n _ _ body) ns := take_arguments' body (n :: ns)
| e' ns := (ns, e')

meta_definition mk_local (n : name) : expr :=
  expr.local_const n n binder_info.default (expr.const n [])

meta_definition take_arguments : expr → (list name × expr)
| e :=
  have res : _, from take_arguments' e [],
  have arg_names : _, from list.reverse (prod.pr1 res),
  have locals : _, from list.map mk_local arg_names,
  (arg_names, expr.instantiate_vars (prod.pr2 res) locals)

meta_definition compile_decl (decl_name : name) (e : expr) : format :=
  have arity : nat, from get_arity e,
  have args_and_body : _, from take_arguments e,
  have ir : _, from compile_decl_to_ir decl_name arity (prod.pr2 args_and_body),
  unwrap_or_else ir format_ir (fun e, error.cases_on e (fun s, format.of_string s))

end native
