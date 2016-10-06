import init.meta.format
import init.meta.expr
import init.string
import system.IO
import system.result
import native.ir
import native.format
import init.state

namespace native

-- builtin stuff
meta constant is_internal_cnstr : expr → option unsigned
meta constant is_internal_cases : expr → option unsigned
meta constant is_internal_proj : expr → option unsigned
meta constant get_nat_value : expr → option nat
meta constant get_builtin : name → option (name × nat)

inductive error
| string : string -> error
| many : list error -> error

attribute [reducible]
definition result (A : Type*) :=
  system.result error A

meta definition arity_map : Type :=
  rb_map name nat

meta definition get_arity : expr -> nat
| (expr.lam _ _ _ body) := 1 + get_arity body
| _ := 0

meta definition mk_arity_map : list (name × expr) -> arity_map
| [] := rb_map.mk name nat
| ((n, body) :: rest) := rb_map.insert (mk_arity_map rest) n (get_arity body)

@[reducible] meta definition ir_compiler (A : Type) :=
  stateT arity_map result A

-- An `exotic` monad combinator that accumulates errors.
meta definition sequence_err : list (ir_compiler format) → ir_compiler (list format × list error)
| [] := return ([], [])
| (action :: remaining) :=
  fun s, match sequence_err remaining s with
    | system.result.err e := system.result.err e
    | system.result.ok ((res, errs), s') := match action s with
      | system.result.err e := system.result.ok ((res, e :: errs), s')
      | system.result.ok (v, s'') := system.result.ok ((v :: res, errs), s'')
      end
    end

-- meta lemma sequence_err_always_ok :
--   forall xs v s s', sequence_err xs s = system.result.ok (v, s') := sorry

meta definition lift {A} (action : result A) : ir_compiler A :=
  fun s, action >>= fun a, return (a, s)

meta definition mk_error {T} : string -> ir_compiler T :=
  fun s, lift (system.result.err $ error.string s)

meta definition lookup_arity (n : name) : ir_compiler nat := do
  map <- stateT.read,
  match rb_map.find map n with
  | option.none := mk_error $ "could not find arity for: " ++ to_string n
  | option.some n := return n
  end

meta definition mk_nat_literal (n : nat) : ir_compiler ir.expr :=
  return (ir.expr.lit $ ir.literal.nat n)

-- HELPERS --
meta definition assert_name : ir.expr → ir_compiler name
| (ir.expr.locl n) := lift $ system.result.ok n
| (ir.expr.call _ _) := mk_error "expected name, found: call "
| (ir.expr.lit _) := mk_error "expected name, found: lit "
| (ir.expr.mk_object _ _) := mk_error "expected name, found: obj "
| (ir.expr.global _) := mk_error "expected local, found global"
| (ir.expr.block _) := mk_error "expected local, found block"
| (ir.expr.project _ _) := mk_error "expected name, found project"
| (ir.expr.panic _) := mk_error "expected name, found panic"
| (ir.expr.mk_native_closure _ _) := mk_error "expected name, found native closure"

meta definition mk_local (n : name) : expr :=
  expr.local_const n n binder_info.default (expr.const n [])

meta definition mk_call (head : name) (args : list ir.expr) : ir_compiler ir.expr :=
  let args'' := list.map assert_name args
  in do
    args' <- monad.sequence args'',
    return (ir.expr.call head args')

meta def mk_under_sat_call (head : name) (args : list ir.expr) : ir_compiler ir.expr :=
let args'' := list.map assert_name args in do
    args' <- monad.sequence args'',
    return $ ir.expr.mk_native_closure head args'

-- meta def mk_over_sat_call

meta def compile_call (head : name) (arity : nat) (args : list ir.expr) : ir_compiler ir.expr := do
  if list.length args = arity
  then mk_call head args
  else if list.length args < arity
  then mk_under_sat_call head args
  else (return $ ir.expr.call "case3" [])

meta definition mk_object (arity : unsigned) (args : list ir.expr) : ir_compiler ir.expr :=
  let args'' := list.map assert_name args
  in do args' <- monad.sequence args'',
        lift (system.result.ok $ ir.expr.mk_object (unsigned.to_nat arity) args')

meta definition is_return (n : name) : bool :=
  decidable.to_bool $ `native_compiler.return = n

meta definition one_or_error (args : list expr) : ir_compiler expr :=
match args with
| ((h : expr) :: []) := lift $ system.result.ok h
| _ := mk_error "internal invariant violated, should only have one argument"
end

meta def panic (msg : string) : ir_compiler ir.expr :=
  return $ ir.expr.panic msg

-- END HELPERS --

meta def compile_case (case : expr) : ir_compiler ir.expr :=
  mk_error "failed to make case"

meta def compile_cases_on_to_ir_expr
    (scrutinee : name)
    (cases : list expr)
    (action : expr -> ir_compiler ir.expr) : ir_compiler ir.expr := do
    default <- panic "default case should never be reached",
    return (ir.expr.block $ (ir.stmt.switch scrutinee [] (ir.stmt.e default)))

-- this code isnt' great working around the semi-functional frontend
meta definition compile_expr_app_to_ir_expr
  (head : expr)
  (args : list expr)
  (action : expr -> ir_compiler ir.expr) : ir_compiler ir.expr := do
    args' <- monad.sequence $ list.map action args,
    if expr.is_constant head = bool.tt
    then if is_return (expr.const_name head) = bool.tt
    then do
      rexp <- one_or_error args,
      (ir.expr.block ∘ ir.stmt.return) <$> action rexp
    else match is_internal_cnstr head with
    | option.some n := mk_object n args'
    | option.none := match is_internal_cases head with
    | option.some n := compile_cases_on_to_ir_expr (expr.const_name head) args action
    | option.none := match get_builtin (expr.const_name head) with
      | option.some (n, arity) := compile_call n arity args'
      | option.none := do
        arity <- lookup_arity (expr.const_name head),
        compile_call (expr.const_name head) arity args'
      end
    end end
    else (mk_error ("unsupported call position" ++ (to_string head)))

meta definition compile_expr_macro_to_ir_expr (e : expr) : ir_compiler ir.expr :=
  match native.get_nat_value e with
  | option.none := mk_error "unsupported macro"
  | option.some n := mk_nat_literal n
  end

meta definition compile_local (n : name) : ir_compiler name :=
  return $ (mk_str_name "_$local$_" (name.to_string_with_sep "_" n))

meta definition compile_expr_to_ir_expr : expr → ir_compiler ir.expr
| (expr.const n ls) :=
  match native.is_internal_cnstr (expr.const n ls) with
  | option.none := pure $ ir.expr.global n
  | option.some arity := pure $ ir.expr.mk_object (unsigned.to_nat arity) []
  end
| (expr.var i) := mk_error "there should be no bound variables in compiled terms"
| (expr.sort _) := mk_error "found sort"
| (expr.mvar _ _) := mk_error "unexpected meta-variable in expr"
| (expr.local_const n _ _ _) := ir.expr.locl <$> compile_local n
| (expr.app f x) :=
  let head := expr.get_app_fn (expr.app f x),
      args := expr.get_app_args (expr.app f x)
  in compile_expr_app_to_ir_expr head args compile_expr_to_ir_expr
| (expr.lam _ _ _ _) := mk_error "found lam"
| (expr.pi _ _ _ _) := mk_error "found pi"
| (expr.elet n _ v body) := mk_error "internal error: can not translate let binding into a ir_expr"
| (expr.macro d sz args) := compile_expr_macro_to_ir_expr (expr.macro d sz args)

meta definition compile_expr_to_ir_stmt : expr -> ir_compiler ir.stmt
| (expr.pi _ _ _ _) := mk_error "found pi, should not be translating a Pi for any reason (yet ...)"
| (expr.elet n _ v body) := do
  n' <- compile_local n,
  v' <- compile_expr_to_ir_expr v,
  body' <- compile_expr_to_ir_stmt (expr.instantiate_vars body [mk_local n]),
  return (ir.stmt.letb n' v' body')
| e' := ir.stmt.e <$> compile_expr_to_ir_expr e'

definition repeat {A : Type} : nat -> A -> list A
| 0 _ := []
| (n + 1) a := a :: repeat n a

definition zip {A B : Type} : list A → list B → list (A × B)
| [] [] := []
| [] (y :: ys) := []
| (x :: xs) [] := []
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys

meta definition compile_decl_to_ir (decl_name : name) (args : list name) (body : expr) : ir_compiler ir.decl := do
  body' <- compile_expr_to_ir_stmt body,
  let params := (zip args (repeat (list.length args) (ir.ty.ref ir.ty.object))) in
  pure (ir.decl.mk decl_name params ir.ty.object body')

definition unwrap_or_else {T R : Type} : result T → (T → R) → (error -> R) -> R
| (system.result.err e) f err := err e
| (system.result.ok t) f err := f t

-- TODO: fix naming here
private meta definition take_arguments' : expr → list name → (list name × expr)
| (expr.lam n _ _ body) ns := take_arguments' body (n :: ns)
| e' ns := (ns, e')

meta definition take_arguments (e : expr) : (list name × expr) :=
  let res := take_arguments' e [],
      arg_names := prod.fst res,
      locals := list.map mk_local arg_names
  in (arg_names, expr.instantiate_vars (prod.snd res) (list.reverse locals))

meta def replace_main (n : name) : name :=
     if n = `main
     then "___lean__main"
     else n

meta definition compile_decl (decl_name : name) (e : expr) : ir_compiler format :=
  let arity := get_arity e,
      (args, body) := take_arguments e in do
      ir <- compile_decl_to_ir (replace_main decl_name) args body,
      return $ format_cpp.decl ir

meta definition compile' : list (name × expr) → list (ir_compiler format)
| [] := []
| ((n, e) :: rest) := do
  let decl := (fun d, d ++ format.line ++ format.line) <$> compile_decl n e
  in decl :: (compile' rest)

meta def format_error : error → format
| (error.string s) := to_fmt s
| (error.many es) := format_concat (list.map format_error es)

meta definition compile (procs : list (name × expr)) : format :=
  let arities := mk_arity_map procs in
  match sequence_err (compile' procs) arities with
  | system.result.err e := to_fmt "ERRRROR"
  | system.result.ok ((decls, errs), _) :=
    if list.length errs = 0
    then format_concat decls
    else format_error (error.many errs)
  end

end native
