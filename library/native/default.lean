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

inductive builtin
| cfun : name -> nat -> builtin
| cases : name -> nat -> builtin
| vm : name -> builtin

meta constant get_builtin : name → option builtin

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
  system.resultT (state arity_map) error A

-- An `exotic` monad combinator that accumulates errors.

meta def run {M E A} (res : system.resultT M E A) : M (system.result E A) :=
  match res with
  | (| action |) := action
  end

meta definition sequence_err : list (ir_compiler format) → ir_compiler (list format × list error)
| [] := return ([], [])
| (action :: remaining) :=
    (| fun s,
       match (run (sequence_err remaining)) s with
       | (system.result.err e, s') := (system.result.err e, s)
       | (system.result.ok (res, errs), s') :=
         match (run action) s' with
         | (system.result.err e, s'') := (system.result.ok (res, e :: errs), s'')
         | (system.result.ok v, s'') := (system.result.ok (v :: res, errs), s'')
         end
         end
     |)

-- meta lemma sequence_err_always_ok :
--   forall xs v s s', sequence_err xs s = system.result.ok (v, s') := sorry

meta definition lift_result {A} (action : result A) : ir_compiler A :=
  (| fun s, (action, s) |)

meta def lift {A} (action : state arity_map A) : ir_compiler A :=
  (| fmap (fun (a : A), system.result.ok a) action |)

meta definition mk_local (n : name) : expr :=
expr.local_const n n binder_info.default (expr.const n [])

-- TODO: fix naming here
private meta definition take_arguments' : expr → list name → (list name × expr)
| (expr.lam n _ _ body) ns := take_arguments' body (n :: ns)
| e' ns := (ns, e')

meta definition take_arguments (e : expr) : (list name × expr) :=
let res := take_arguments' e [],
arg_names := prod.fst res,
locals := list.map mk_local arg_names
in (arg_names, expr.instantiate_vars (prod.snd res) (list.reverse locals))

-- meta def lift_state {A} (action : state arity_map A) : ir_compiler A :=
--   fun (s : arity_map), match action s with
--   | (a, s) := (return a, s)
--   end

meta definition mk_error {T} : string -> ir_compiler T :=
  fun s, lift_result (system.result.err $ error.string s)

meta definition lookup_arity (n : name) : ir_compiler nat := do
  map <- lift state.read,
  match rb_map.find map n with
  | option.none := mk_error $ "could not find arity for: " ++ to_string n
  | option.some n := return n
  end

meta definition mk_nat_literal (n : nat) : ir_compiler ir.expr :=
  return (ir.expr.lit $ ir.literal.nat n)

definition repeat {A : Type} : nat -> A -> list A
| 0 _ := []
| (n + 1) a := a :: repeat n a

definition zip {A B : Type} : list A → list B → list (A × B)
| [] [] := []
| [] (y :: ys) := []
| (x :: xs) [] := []
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys

private def upto' : ℕ → list ℕ
| 0 := []
| (n + 1) := n :: upto' n

def upto (n : ℕ) : list ℕ :=
  list.reverse $ upto' n

def label {A : Type} (xs : list A) : list (nat × A) :=
  zip (upto (list.length xs)) xs

-- lemma label_size_eq :
--   forall A (xs : list A),
--   list.length (label xs) = list.length xs :=
-- begin
--   intros,
--   induction xs,
--   apply sorry
--   apply sorry
-- end

-- HELPERS --
meta definition assert_name : ir.expr → ir_compiler name
| (ir.expr.locl n) := lift_result $ system.result.ok n
| (ir.expr.call _ _) := mk_error "expected name, found: call "
| (ir.expr.lit _) := mk_error "expected name, found: lit "
| (ir.expr.mk_object _ _) := mk_error "expected name, found: obj "
| (ir.expr.global _) := mk_error "expected local, found global"
| (ir.expr.block _) := mk_error "expected local, found block"
| (ir.expr.project _ _) := mk_error "expected name, found project"
| (ir.expr.panic _) := mk_error "expected name, found panic"
| (ir.expr.mk_native_closure _ _) := mk_error "expected name, found native closure"
| (ir.expr.invoke _ _) := mk_error "expected name, found invoke"
| (ir.expr.assign _ _) := mk_error "expected name, found assign"
| ir.expr.uninitialized := mk_error "expected name, found assign"

meta definition assert_expr : ir.stmt -> ir_compiler ir.expr
| (ir.stmt.e exp) := return exp
| s := mk_error ("internal invariant violated, found: " ++ (to_string (format_cpp.stmt s)))


meta definition mk_call (head : name) (args : list ir.expr) : ir_compiler ir.expr :=
  let args'' := list.map assert_name args
  in do
    args' <- monad.sequence args'',
    return (ir.expr.call head args')

meta def mk_under_sat_call (head : name) (args : list ir.expr) : ir_compiler ir.expr :=
let args'' := list.map assert_name args in do
    args' <- monad.sequence args'',
    return $ ir.expr.mk_native_closure head args'

meta def bind_value (val : ir.expr) (body : name → ir_compiler ir.stmt) : ir_compiler ir.stmt :=
let n := `scrut -- maybe generate fresh name here?
in ir.stmt.letb n ir.ty.object val <$> (body n)

-- not in love with this --solution-- hack, revisit
meta definition compile_local (n : name) : ir_compiler name :=
return $ (mk_str_name "_$local$_" (name.to_string_with_sep "_" n))

meta definition mk_invoke (loc : name) (args : list ir.expr) : ir_compiler ir.expr :=
let args'' := list.map assert_name args
in do
  args' <- monad.sequence args'',
  loc' <- compile_local loc,
  lift_result (system.result.ok $ ir.expr.invoke loc' args')

meta def mk_over_sat_call (head : name) (fst snd : list ir.expr) : ir_compiler ir.expr :=
let fst' := list.map assert_name fst,
    snd' := list.map assert_name snd in do
  args' <- monad.sequence fst',
  args'' <- monad.sequence snd',
  invoke <- ir.stmt.e <$> (mk_invoke `foo (fmap ir.expr.locl args'')),
  return $ ir.expr.block (ir.stmt.seq [
    ir.stmt.letb `foo ir.ty.object (ir.expr.call head args') ir.stmt.nop,
    invoke
  ])

meta definition is_return (n : name) : bool :=
decidable.to_bool $ `native_compiler.return = n

meta def compile_call (head : name) (arity : nat) (args : list ir.expr) : ir_compiler ir.expr := do
  if list.length args = arity
  then mk_call head args
  else if list.length args < arity
  then mk_under_sat_call head args
  else mk_over_sat_call head (list.taken arity args) (list.dropn arity args)

meta definition mk_object (arity : unsigned) (args : list ir.expr) : ir_compiler ir.expr :=
  let args'' := list.map assert_name args
  in do args' <- monad.sequence args'',
        lift_result (system.result.ok $ ir.expr.mk_object (unsigned.to_nat arity) args')

meta definition one_or_error (args : list expr) : ir_compiler expr :=
match args with
| ((h : expr) :: []) := lift_result $ system.result.ok h
| _ := mk_error "internal invariant violated, should only have one argument"
end

meta def panic (msg : string) : ir_compiler ir.expr :=
  return $ ir.expr.panic msg

-- END HELPERS --

meta def bind_case_fields' (scrut : name) : list (nat × name) -> ir.stmt -> ir_compiler ir.stmt
| [] body := return body
| ((n, f) :: fs) body := do
  loc <- compile_local f,
  ir.stmt.letb f ir.ty.object (ir.expr.project scrut n) <$> (bind_case_fields' fs body)

meta def bind_case_fields (scrut : name) (fs : list name) (body : ir.stmt) : ir_compiler ir.stmt :=
  bind_case_fields' scrut (label fs) body

meta def mk_cases_on (case_name scrut : name) (cases : list (nat × ir.stmt)) (default : ir.stmt) : ir.stmt :=
ir.stmt.seq [
  ir.stmt.letb `ctor_index ir.ty.int (ir.expr.call `cidx [scrut]) ir.stmt.nop,
  ir.stmt.switch `ctor_index cases default
]

meta def compile_cases (action : expr → ir_compiler ir.stmt) (scrut : name)
: list (nat × expr) → ir_compiler (list (nat × ir.stmt))
| [] := return []
| ((n, body) :: cs) := do
  let (fs, body') := take_arguments body in do
  body'' <- action body',
  cs' <- compile_cases cs,
  case <- bind_case_fields scrut fs body'',
  return $ (n, case) :: cs'

meta def compile_cases_on_to_ir_expr
    (case_name : name)
    (cases : list expr)
    (action : expr -> ir_compiler ir.stmt) : ir_compiler ir.expr := do
    default <- panic "default case should never be reached",
    match cases with
    | [] := mk_error $ "found " ++ to_string case_name ++ "applied to zero arguments"
    | (h :: cs) := do
      ir_scrut <- action h >>= assert_expr,
      ir.expr.block <$> bind_value ir_scrut (fun scrut, do
        cs' <- compile_cases action scrut (label cs),
        return (mk_cases_on case_name scrut cs' (ir.stmt.e default)))
    end

meta def bind_builtin_case_fields' (scrut : name) : list (nat × name) -> ir.stmt -> ir_compiler ir.stmt
| [] body := return body
| ((n, f) :: fs) body := do
  loc <- compile_local f,
  ir.stmt.letb loc ir.ty.object (ir.expr.project scrut n) <$> (bind_builtin_case_fields' fs body)

meta def bind_builtin_case_fields (scrut : name) (fs : list name) (body : ir.stmt) : ir_compiler ir.stmt :=
bind_builtin_case_fields' scrut (label fs) body

meta def compile_builtin_cases (action : expr → ir_compiler ir.stmt) (scrut : name)
  : list (nat × expr) → ir_compiler (list (nat × ir.stmt))
| [] := return []
| ((n, body) :: cs) :=
  let (fs, body') := take_arguments body in do
  body'' <- action body',
  cs' <- compile_builtin_cases cs,
  case <- bind_builtin_case_fields scrut fs body'',
  return $ (n, case) :: cs'

meta def in_lean_ns (n : name) : name :=
  mk_simple_name ("lean::" ++ name.to_string_with_sep "_" n)

meta def mk_builtin_cases_on (case_name scrut : name) (cases : list (nat × ir.stmt)) (default : ir.stmt) : ir.stmt :=
-- replace `ctor_index with a generated name
ir.stmt.seq [
  ir.stmt.letb `buffer ir.ty.object_buffer ir.expr.uninitialized ir.stmt.nop,
  ir.stmt.letb `ctor_index ir.ty.int (ir.expr.call (in_lean_ns case_name) [scrut, `buffer]) ir.stmt.nop,
  ir.stmt.switch `ctor_index cases default
]

meta def compile_builtin_cases_on_to_ir_expr
(case_name : name)
(cases : list expr)
(action : expr -> ir_compiler ir.stmt) : ir_compiler ir.expr := do
default <- panic "default case should never be reached",
match cases with
| [] := mk_error $ "found " ++ to_string case_name ++ "applied to zero arguments"
| (h :: cs) := do
  ir_scrut <- action h >>= assert_expr,
  ir.expr.block <$> bind_value ir_scrut (fun scrut, do
    cs' <- compile_builtin_cases action scrut (label cs),
    return (mk_builtin_cases_on case_name scrut cs' (ir.stmt.e default)))
end

-- this code isnt' great working around the semi-functional frontend
meta definition compile_expr_app_to_ir_expr
  (head : expr)
  (args : list expr)
  (action : expr -> ir_compiler ir.stmt) : ir_compiler ir.expr := do
    if expr.is_constant head = bool.tt
    then if is_return (expr.const_name head) = bool.tt
    then do
      rexp <- one_or_error args,
      (ir.expr.block ∘ ir.stmt.return) <$> ((action rexp) >>= assert_expr)
    else match is_internal_cnstr head with
    | option.some n := do
      args' <- monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
      mk_object n args'
    | option.none := match is_internal_cases head with
    | option.some n := compile_cases_on_to_ir_expr (expr.const_name head) args action
    | option.none := match get_builtin (expr.const_name head) with
      | option.some builtin :=
        match builtin with
        | builtin.vm n := mk_error "vm"
        | builtin.cfun n arity := do
          args' <- monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
          compile_call n arity args'
        | builtin.cases n arity :=
          compile_builtin_cases_on_to_ir_expr (expr.const_name head) args action
        end
      | option.none := do
        args' <- monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
        arity <- lookup_arity (expr.const_name head),
        compile_call (expr.const_name head) arity args'
      end
    end end
    else if expr.is_local_constant head
    then do
      args' <- monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
      mk_invoke (expr.local_uniq_name head) args'
    else (mk_error ("unsupported call position" ++ (to_string head)))

meta definition compile_expr_macro_to_ir_expr (e : expr) : ir_compiler ir.expr :=
  match native.get_nat_value e with
  | option.none := mk_error "unsupported macro"
  | option.some n := mk_nat_literal n
  end

meta definition compile_expr_to_ir_expr (action : expr -> ir_compiler ir.stmt): expr → ir_compiler ir.expr
| (expr.const n ls) :=
  match native.is_internal_cnstr (expr.const n ls) with
  | option.none :=
    -- TODO, do I need to case on arity here? I should probably always emit a call
    match get_builtin n with
    | option.some (builtin.cfun n' arity) :=
      compile_call n arity []
    | _ :=
      if n = "_neutral_"
      then (pure $ ir.expr.mk_object 0 [])
      else do
        arity <- lookup_arity n,
        compile_call n arity []
    end
  | option.some arity := pure $ ir.expr.mk_object (unsigned.to_nat arity) []
  end
| (expr.var i) := mk_error "there should be no bound variables in compiled terms"
| (expr.sort _) := mk_error "found sort"
| (expr.mvar _ _) := mk_error "unexpected meta-variable in expr"
| (expr.local_const n _ _ _) := ir.expr.locl <$> compile_local n
| (expr.app f x) :=
  let head := expr.get_app_fn (expr.app f x),
      args := expr.get_app_args (expr.app f x)
  in compile_expr_app_to_ir_expr head args action
| (expr.lam _ _ _ _) := mk_error "found lam"
| (expr.pi _ _ _ _) := mk_error "found pi"
| (expr.elet n _ v body) := mk_error "internal error: can not translate let binding into a ir_expr"
| (expr.macro d sz args) := compile_expr_macro_to_ir_expr (expr.macro d sz args)

meta definition compile_expr_to_ir_stmt : expr -> ir_compiler ir.stmt
| (expr.pi _ _ _ _) := mk_error "found pi, should not be translating a Pi for any reason (yet ...)"
| (expr.elet n _ v body) := do
  n' <- compile_local n,
  v' <- compile_expr_to_ir_expr compile_expr_to_ir_stmt v,
  body' <- compile_expr_to_ir_stmt (expr.instantiate_vars body [mk_local n]),
  -- not the best solution, here need to think hard about how to prevent thing, more aggressive anf? 
  match v' with
  | ir.expr.block stmt := return (ir.stmt.seq [ir.stmt.letb n' ir.ty.object ir.expr.uninitialized ir.stmt.nop, body'])
  | _ := return (ir.stmt.letb n' ir.ty.object v' body')
  end
| e' := ir.stmt.e <$> compile_expr_to_ir_expr compile_expr_to_ir_stmt e'

meta definition compile_decl_to_ir (decl_name : name) (args : list name) (body : expr) : ir_compiler ir.decl := do
  body' <- compile_expr_to_ir_stmt body,
  let params := (zip args (repeat (list.length args) (ir.ty.ref ir.ty.object))) in
  pure (ir.decl.mk decl_name params ir.ty.object body')

definition unwrap_or_else {T R : Type} : result T → (T → R) → (error -> R) -> R
| (system.result.err e) f err := err e
| (system.result.ok t) f err := f t


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
  -- Put this in a combinator or something ...
  match run (sequence_err (compile' procs)) arities with
  | (system.result.err e, s) := to_fmt "ERRRROR"
  | (system.result.ok (decls, errs), s) :=
    if list.length errs = 0
    then format_concat decls
    else format_error (error.many errs)
  end

end native
