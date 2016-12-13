/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.format
import init.meta.expr
import init.category.state
import init.data.string
import init.data.list.instances

import init.native.ir
import init.native.ir.compiler
import init.native.format
import init.native.internal
import init.native.anf
import init.native.cf
import init.native.pass
import init.native.util
import init.native.config
import init.native.result
import init.native.attributes
import init.debugger
import init.debugger.cli

set_option debugger true

namespace native

meta def trace_ir (s : string) : ir_compiler unit := do
  conf <- configuration,
  if config.debug conf
  then trace s (return ())
  else return ()

meta def run {M E A} (res : native.resultT M E A) : M (native.result E A) :=
  match res with
  | ⟨action⟩ := action
  end

-- An `exotic` monad combinator that accumulates errors.
meta def sequence_err : list (ir_compiler ir.item) → ir_compiler (list ir.item × list error)
| [] := return ([], [])
| (action :: remaining) :=
    ⟨ fun s,
       match (run (sequence_err remaining)) s with
       | (native.result.err e, s') := (native.result.err e, s)
       | (native.result.ok (res, errs), s') :=
         match (run action) s' with
         | (native.result.err e, s'') := (native.result.ok (res, e :: errs), s'')
         | (native.result.ok v, s'') := (native.result.ok (v :: res, errs), s'')
         end
         end
     ⟩

meta def lift_result {A} (action : ir.result A) : ir_compiler A :=
  ⟨fun s, (action, s)⟩

-- TODO: fix naming here
private meta def take_arguments' : expr → list name → (list name × expr)
| (expr.lam n _ _ body) ns := take_arguments' body (n :: ns)
| e' ns := (ns, e')


meta def fresh_name : ir_compiler name := do
  (ctxt, conf, map, counter) ← lift state.read,
  let fresh := name.mk_numeral (unsigned.of_nat counter) `native._ir_compiler_
    lift $ state.write (ctxt, conf, map, counter + 1),
    return fresh

meta def take_arguments (e : expr) : ir_compiler (list name × expr) :=
  let (arg_names, body) := take_arguments' e [] in do
  fresh_names ← monad.mapm (fun x, fresh_name) arg_names,
  let locals := list.map mk_local fresh_names,
  return $ (fresh_names, expr.instantiate_vars body (list.reverse locals))

meta def mk_error {T} : string → ir_compiler T :=
  fun s, do
  lift_result (native.result.err $ error.string s)

meta def lookup_arity (n : name) : ir_compiler nat := do
  map ← arities,
  if n = `nat.cases_on
  then pure 2
  else
  match rb_map.find map n with
  | option.none := mk_error $ "could not find arity for: " ++ to_string n
  | option.some n := return n
  end

meta def mk_nat_literal (n : nat) : ir_compiler ir.expr :=
  return (ir.expr.lit $ ir.literal.nat n)

private def upto' : ℕ → list ℕ
| 0 := []
| (n + 1) := n :: upto' n

def upto (n : ℕ) : list ℕ :=
  list.reverse $ upto' n

def label {A : Type} (xs : list A) : list (nat × A) :=
  list.zip (upto (list.length xs)) xs

open tactic

-- ask about this one

-- lemma label_size_eq :
--    forall A (xs : list A),
--    list.length (label xs) = list.length xs :=
-- begin
--   intros,
--   induction xs,
--   unfold label,
-- end

-- HELPERS --
meta def assert_name : ir.expr → ir_compiler name
| (ir.expr.locl n) := lift_result $ native.result.ok n
| e := mk_error $ "expected name found: " ++ to_string (format_cpp.expr e)

meta def assert_expr : ir.stmt → ir_compiler ir.expr
| (ir.stmt.e exp) := return exp
| s := mk_error ("internal invariant violated, found: " ++ to_string (format_cpp.stmt s))

meta def mk_ir_call (head : name) (args : list ir.expr) : ir_compiler ir.expr :=
  let args'' := list.map assert_name args
  in do
    args' ← monad.sequence args'',
    return (ir.expr.call head args')

meta def mk_under_sat_call (head : name) (args : list ir.expr) : ir_compiler ir.expr :=
let args'' := list.map assert_name args in do
    args' ← monad.sequence args'',
    return $ ir.expr.mk_native_closure head args'

meta def bind_value_with_ty (val : ir.expr) (ty : ir.ty) (body : name → ir_compiler ir.stmt) : ir_compiler ir.stmt := do
  fresh ← fresh_name,
  ir.stmt.letb fresh ty val <$> (body fresh)

meta def bind_value (val : ir.expr) (body : name → ir_compiler ir.stmt) : ir_compiler ir.stmt :=
  bind_value_with_ty val (ir.ty.object none) body

-- not in love with this --solution-- hack, revisit
meta def compile_local (n : name) : ir_compiler name :=
return $ (mk_str_name "_$local$_" (name.to_string_with_sep "_" n))

meta def mk_invoke (loc : name) (args : list ir.expr) : ir_compiler ir.expr :=
let args'' := list.map assert_name args
in do
  args' ← monad.sequence args'',
  loc' ← compile_local loc,
  lift_result (native.result.ok $ ir.expr.invoke loc' args')

meta def mk_over_sat_call (head : name) (fst snd : list ir.expr) : ir_compiler ir.stmt :=
let fst' := list.map assert_name fst,
    snd' := list.map assert_name snd in do
  args' ← monad.sequence fst',
  args'' ← monad.sequence snd',
  fresh ← fresh_name,
  locl ← compile_local fresh,
  invoke ← ir.stmt.e <$> (mk_invoke fresh (ir.expr.locl <$> args'')),
  return $ (ir.stmt.seq [
    ir.stmt.letb locl (ir.ty.object none) (ir.expr.call head args') ir.stmt.nop,
    invoke
  ])

meta def is_return (n : name) : bool :=
`native_compiler.return = n

meta def compile_call (head : name) (arity : nat) (args : list ir.expr) : ir_compiler ir.stmt := do
  trace_ir $ "compile_call: " ++ to_string head,
  if list.length args = arity
  then ir.stmt.e <$> mk_ir_call head args
  else if list.length args < arity
  then ir.stmt.e <$> mk_under_sat_call head args
  else mk_over_sat_call head (list.take arity args) (list.drop arity args)

meta def mk_object (arity : unsigned) (args : list ir.expr) : ir_compiler ir.expr :=
  let args'' := list.map assert_name args
  in do args' ← monad.sequence args'',
        lift_result (native.result.ok $ ir.expr.mk_object (unsigned.to_nat arity) args')

meta def one_or_error (args : list expr) : ir_compiler expr :=
match args with
| ((h : expr) :: []) := lift_result $ native.result.ok h
| _ := mk_error "internal invariant violated, should only have one argument"
end

meta def panic (msg : string) : ir_compiler ir.expr :=
  return $ ir.expr.panic msg

-- END HELPERS --

meta def bind_case_fields' (scrut : name) : list (nat × name) → ir.stmt → ir_compiler ir.stmt
| [] body := return body
| ((n, f) :: fs) body := do
  loc ← compile_local f,
  ir.stmt.letb f (ir.ty.object none) (ir.expr.project scrut n) <$> (bind_case_fields' fs body)

meta def bind_case_fields (scrut : name) (fs : list name) (body : ir.stmt) : ir_compiler ir.stmt :=
  bind_case_fields' scrut (label fs) body

meta def mk_cases_on (case_name scrut : name) (cases : list (nat × ir.stmt)) (default : ir.stmt) : ir.stmt :=
ir.stmt.seq [
  ir.stmt.letb `ctor_index (ir.ty.name `unsigned) (ir.expr.call `cidx [scrut]) ir.stmt.nop,
  ir.stmt.switch `ctor_index cases default
]

meta def compile_cases (action : expr → ir_compiler ir.stmt) (scrut : name)
: list (nat × expr) → ir_compiler (list (nat × ir.stmt))
| [] := return []
| ((n, body) :: cs) := do
  (fs, body') ← take_arguments body,
  body'' ← action body',
  cs' ← compile_cases cs,
  case ← bind_case_fields scrut fs body'',
  return $ (n, case) :: cs'

meta def compile_cases_on_to_ir_stmt
    (case_name : name)
    (cases : list expr)
    (action : expr → ir_compiler ir.stmt) : ir_compiler ir.stmt := do
    default ← panic "default case should never be reached",
    match cases with
    | [] := mk_error $ "found " ++ to_string case_name ++ " applied to zero arguments"
    | (h :: cs) := do
      ir_scrut ← action h >>= assert_expr,
      bind_value ir_scrut (fun scrut, do
        cs' ← compile_cases action scrut (label cs),
        return (mk_cases_on case_name scrut cs' (ir.stmt.e default)))
    end

meta def bind_builtin_case_fields' (scrut : name) : list (nat × name) → ir.stmt → ir_compiler ir.stmt
| [] body := return body
| ((n, f) :: fs) body := do
  loc ← compile_local f,
  ir.stmt.letb loc (ir.ty.object none) (ir.expr.project scrut n) <$> (bind_builtin_case_fields' fs body)

meta def bind_builtin_case_fields (scrut : name) (fs : list name) (body : ir.stmt) : ir_compiler ir.stmt :=
bind_builtin_case_fields' scrut (label fs) body

meta def compile_builtin_cases (action : expr → ir_compiler ir.stmt) (scrut : name)
  : list (nat × expr) → ir_compiler (list (nat × ir.stmt))
| [] := return []
| ((n, body) :: cs) := do
  (fs, body') ← take_arguments body,
  body'' ← action body',
  cs' ← compile_builtin_cases cs,
  case ← bind_builtin_case_fields scrut fs body'',
  return $ (n, case) :: cs'

meta def in_lean_ns (n : name) : name :=
  mk_simple_name ("lean::" ++ name.to_string_with_sep "_" n)

meta def mk_builtin_cases_on (case_name scrut : name) (cases : list (nat × ir.stmt)) (default : ir.stmt) : ir.stmt :=
-- replace `ctor_index with a generated name
ir.stmt.seq [
  ir.stmt.letb `buffer ir.ty.object_buffer ir.expr.uninitialized ir.stmt.nop,
  ir.stmt.letb `ctor_index (ir.ty.name `unsigned) (ir.expr.call (in_lean_ns case_name) [scrut, `buffer]) ir.stmt.nop,
  ir.stmt.switch `ctor_index cases default
]

meta def compile_builtin_cases_on_to_ir_expr
(case_name : name)
(cases : list expr)
(action : expr → ir_compiler ir.stmt) : ir_compiler ir.stmt := do
default ← panic "default case should never be reached",
match cases with
| [] := mk_error $ "found " ++ to_string case_name ++ " applied to zero arguments"
| (h :: cs) := do
  ir_scrut ← action h >>= assert_expr,
  bind_value ir_scrut (fun scrut, do
    cs' ← compile_builtin_cases action scrut (label cs),
    return (mk_builtin_cases_on case_name scrut cs' (ir.stmt.e default)))
end

meta def mk_is_simple (scrut : name) : ir.expr :=
  ir.expr.call `is_simple [scrut]

meta def mk_is_zero (n : name) : ir.expr :=
  ir.expr.equals (ir.expr.raw_int 0) (ir.expr.locl n)

meta def mk_cidx (obj : name) : ir.expr :=
  ir.expr.call `cidx [obj]

-- we should add applicative brackets
meta def mk_simple_nat_cases_on (scrut : name) (zero_case succ_case : ir.stmt) : ir_compiler ir.stmt :=
  bind_value_with_ty (mk_cidx scrut) (ir.ty.name `int) (fun cidx,
    bind_value_with_ty (mk_is_zero cidx) (ir.ty.name `bool) (fun is_zero,
    pure $ ir.stmt.ite is_zero zero_case succ_case))

meta def mk_mpz_nat_cases_on (scrut : name) (zero_case succ_case : ir.stmt) : ir_compiler ir.stmt :=
  ir.stmt.e <$> panic "mpz"
  -- this→emit_string("else ");
  -- this→emit_block([&] () {

  --     action(scrutinee);
  --     this→emit_string(") == 0) ");
  --     this→emit_block([&] () {
  --         action(zero_case);
  --         *this→m_output_stream << ";\n";
  --     });
  --     this→emit_string("else ");
  --     this→emit_block([&] () {
  --         action(succ_case);
  --     });
  -- });

meta def mk_nat_cases_on (scrut : name) (zero_case succ_case : ir.stmt) : ir_compiler ir.stmt :=
  bind_value_with_ty (mk_is_simple scrut) (ir.ty.name `bool) (fun is_simple,
    ir.stmt.ite is_simple <$>
      mk_simple_nat_cases_on scrut zero_case succ_case <*>
      mk_mpz_nat_cases_on scrut zero_case succ_case)

meta def assert_two_cases (cases : list expr) : ir_compiler (expr × expr) :=
  match cases with
  | c1 :: c2 :: _ := return (c1, c2)
  | _ := mk_error "nat.cases_on should have exactly two cases"
  end

meta def mk_vm_nat (n : name) : ir.expr :=
  ir.expr.call (in_lean_ns `mk_vm_simple) [n]

meta def compile_succ_case (action : expr → ir_compiler ir.stmt) (scrut : name) (succ_case : expr) : ir_compiler ir.stmt := do
  (fs, body') ← take_arguments succ_case,
  body'' ← action body',
  match fs with
  | pred :: _ := do
    loc ← compile_local pred,
    fresh ← fresh_name,
    bind_value_with_ty (mk_cidx scrut) (ir.ty.name `int) (fun cidx,
      bind_value_with_ty (ir.expr.sub (ir.expr.locl cidx) (ir.expr.raw_int 1)) (ir.ty.name `int) (fun sub,
      pure $ ir.stmt.letb loc (ir.ty.object none) (mk_vm_nat sub) body''
    ))
  | _ := mk_error "compile_succ_case too many fields"
  end

meta def compile_nat_cases_on_to_ir_expr
(case_name : name)
(cases : list expr)
(action : expr → ir_compiler ir.stmt) : ir_compiler ir.stmt :=
  match cases with
  | [] := mk_error $ "found " ++ to_string case_name ++ " applied to zero arguments"
  | (h :: cs) := do
    ir_scrut ← action h >>= assert_expr,
    (zero_case, succ_case) ← assert_two_cases cs,
    trace_ir (to_string zero_case),
    trace_ir (to_string succ_case),
    bind_value ir_scrut (fun scrut, do
      zc ← action zero_case,
      sc ← compile_succ_case action scrut succ_case,
      mk_nat_cases_on scrut zc sc
    )
  end

meta def compile_expr_app_to_ir_stmt
  (head : expr)
  (args : list expr)
  (action : expr → ir_compiler ir.stmt) : ir_compiler ir.stmt := do
    trace_ir (to_string head  ++ to_string args),
    if expr.is_constant head = bool.tt
    then (if is_return (expr.const_name head)
    then do
      rexp ← one_or_error args,
      ir.stmt.return <$> ((action rexp) >>= assert_expr)
    else if is_nat_cases_on (expr.const_name head)
    then compile_nat_cases_on_to_ir_expr (expr.const_name head) args action
    else match is_internal_cnstr head with
    | option.some n := do
      args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
      ir.stmt.e <$> mk_object n args'
    | option.none := match is_internal_cases head with
    | option.some n := compile_cases_on_to_ir_stmt (expr.const_name head) args action
    | option.none := match get_builtin (expr.const_name head) with
      | option.some b :=
        match b with
        | builtin.vm n := mk_error "vm"
        | builtin.cfun n arity := do
          args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
          compile_call n arity args'
        | builtin.cases n arity :=
          compile_builtin_cases_on_to_ir_expr (expr.const_name head) args action
        end
      | option.none := do
        args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
        arity ← lookup_arity (expr.const_name head),
        compile_call (expr.const_name head) arity args'
      end
    end end)
    else if expr.is_local_constant head
    then do
      args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
      ir.stmt.e <$> mk_invoke (expr.local_uniq_name head) args'
    else (mk_error ("unsupported call position" ++ (to_string head)))

meta def compile_expr_macro_to_ir_expr (e : expr) : ir_compiler ir.expr :=
  match native.get_nat_value e with
  | option.none := mk_error "unsupported macro"
  | option.some n := mk_nat_literal n
  end

meta def assign_stmt' (n : name) : ir.stmt → ir_compiler ir.stmt
| (ir.stmt.e e) := do
  pure $ ir.stmt.assign n e
| s := pure s

meta def assign_stmt (n : name) (stmt : ir.stmt) : ir_compiler ir.stmt := do
  n' <- compile_local n,
  st <- assign_stmt' n' stmt,
  pure $ ir.stmt.seq [
    ir.stmt.letb n' (ir.ty.object none) ir.expr.uninitialized ir.stmt.nop,
    st
  ]

meta def compile_expr_to_ir_stmt : expr → ir_compiler ir.stmt
| (expr.const n ls) :=
  match native.is_internal_cnstr (expr.const n ls) with
  | option.none :=
    -- TODO, do I need to case on arity here? I should probably always emit a call
    match get_builtin n with
    | option.some (builtin.cfun n' arity) :=
      compile_call n arity []
    | _ :=
      if n = "_neutral_"
      then (pure $ ir.stmt.e $ ir.expr.mk_object 0 [])
      else do
        arity ← lookup_arity n,
        compile_call n arity []
    end
  | option.some arity := pure $ ir.stmt.e $ ir.expr.mk_object (unsigned.to_nat arity) []
  end
| (expr.var i) := mk_error "there should be no bound variables in compiled terms"
| (expr.sort _) := mk_error "found sort"
| (expr.mvar _ _) := mk_error "unexpected meta-variable in expr"
| (expr.local_const n _ _ _) := ir.stmt.e <$> (ir.expr.locl <$> compile_local n)
| (expr.app f x) :=
  let head := expr.get_app_fn (expr.app f x),
      args := expr.get_app_args (expr.app f x)
  in compile_expr_app_to_ir_stmt head args compile_expr_to_ir_stmt
| (expr.lam _ _ _ _) := mk_error "found lam"
| (expr.pi _ _ _ _) := mk_error "found pi, should not be translating a Pi for any reason (yet ...)"
| (expr.macro d sz args) := ir.stmt.e <$> compile_expr_macro_to_ir_expr (expr.macro d sz args)
| (expr.elet n _ v body) := do
  n' ← compile_local n,
  v' ← compile_expr_to_ir_stmt v,
  assign <- assign_stmt n v',
  body' ← compile_expr_to_ir_stmt (expr.instantiate_vars body [mk_local n]),
  return $ ir.stmt.seq [assign, body']

meta def compile_defn_to_ir (decl_name : name) (args : list name) (body : expr) : ir_compiler ir.defn := do
  body' ← compile_expr_to_ir_stmt body,
  let params := (list.zip args (list.repeat (ir.ty.ref (ir.ty.object none)) (list.length args))) in
  pure (ir.defn.mk decl_name params (ir.ty.object none) body')

def unwrap_or_else {T R : Type} : ir.result T → (T → R) → (error → R) → R
| (native.result.err e) f err := err e
| (native.result.ok t) f err := f t

meta def replace_main (n : name) : name :=
     if n = `main
     then "___lean__main"
     else n

meta def trace_expr (e : expr) : ir_compiler unit :=
  trace ("trace_expr: " ++ to_string e) (return ())

meta def has_ir_refinement (n : name) : ir_compiler (option ir.item) := do
  ctxt <- get_context,
  pure $ ir.lookup_item n ctxt

meta def compile_defn (decl_name : name) (e : expr) : ir_compiler ir.defn := do
  trace_ir (to_string decl_name),
  refinement <- has_ir_refinement decl_name,
  match refinement with
  | some item :=
    match item with
    | ir.item.defn d := (do trace_ir "here", pure d)
    | _ := mk_error "not sure what to do here yet"
    end
  | none :=
    let arity := native.get_arity e in do (args, body) ← take_arguments e,
    compile_defn_to_ir (replace_main decl_name) args body
  end

meta def compile_defns : list procedure → list (ir_compiler ir.item) :=
  fun ps, list.map (fun p, ir.item.defn <$> compile_defn (prod.fst p) (prod.snd p)) ps

meta def mk_builtin_cases_on_proto (n : name) : ir_compiler ir.decl := do
  o <- fresh_name,
  data <- fresh_name,
  return $ ir.decl.mk n [(o, ir.ty.ref (ir.ty.object none)), (data, ir.ty.mut_ref ir.ty.object_buffer)] (ir.ty.name `unsigned)

meta def compile_decl : extern_fn → ir_compiler ir.item
| (in_lean_ns, n, arity) :=
  if is_cases_on (expr.const n [])
  then ir.item.decl <$> mk_builtin_cases_on_proto n
  else (return $ ir.item.decl $ ir.decl.mk n (list.repeat ("", (ir.ty.object none)) (unsigned.to_nat arity)) (ir.ty.object none))

meta def compile_decls : list extern_fn → list (ir_compiler ir.item) :=
  fun xs, list.map compile_decl xs

meta def format_error : error → format
| (error.string s) := to_fmt s
| (error.many es) := format_concat (list.map format_error es)

meta def mk_lean_name (n : name) : ir.expr :=
  ir.expr.constructor (in_lean_ns `name) (name.components n)

meta def emit_declare_vm_builtins : list (name × expr) → ir_compiler (list ir.stmt)
| [] := return []
| ((n, body) :: es) := do
  vm_name ← pure $ (mk_lean_name n),
  tail ← emit_declare_vm_builtins es,
  fresh ← fresh_name,
  let cpp_name := in_lean_ns `name,
  let single_binding := ir.stmt.seq [
    ir.stmt.letb fresh (ir.ty.name cpp_name) vm_name ir.stmt.nop,
    ir.stmt.assign `env (ir.expr.call `add_native [`env, fresh, replace_main n])
 ],
  return $ single_binding :: tail

meta def emit_main (procs : list (name × expr)) : ir_compiler ir.defn := do
  builtins ← emit_declare_vm_builtins procs,
  arity ← lookup_arity `main,
  vm_simple_obj ← fresh_name,
  call_main ← compile_call "___lean__main" arity [ir.expr.locl vm_simple_obj],
  return (ir.defn.mk `main [] ir.ty.int $ ir.stmt.seq ([
    ir.stmt.e $ ir.expr.call (in_lean_ns `initialize) [],
    ir.stmt.letb `env (ir.ty.name (in_lean_ns `environment)) ir.expr.uninitialized ir.stmt.nop
  ] ++ builtins ++ [
    ir.stmt.letb `ios (ir.ty.name (in_lean_ns `io_state)) (ir.expr.call (in_lean_ns `get_global_ios) []) ir.stmt.nop,
    ir.stmt.letb `opts (ir.ty.name (in_lean_ns `options)) (ir.expr.call (in_lean_ns `get_options_from_ios) [`ios]) ir.stmt.nop,
    ir.stmt.letb `S (ir.ty.name (in_lean_ns `vm_state)) (ir.expr.constructor (in_lean_ns `vm_state) [`env, `opts]) ir.stmt.nop,
    ir.stmt.letb `scoped (ir.ty.name (in_lean_ns `scope_vm_state)) (ir.expr.constructor (in_lean_ns `scope_vm_state) [`S]) ir.stmt.nop,
    ir.stmt.assign `g_env (ir.expr.address_of `env),
    ir.stmt.letb vm_simple_obj (ir.ty.object none) (ir.expr.mk_object 0 []) ir.stmt.nop,
    call_main
]))

meta def apply_pre_ir_passes
  (procs : list procedure)
  (conf : config)
  (arity : arity_map) : list procedure :=
  run_passes conf arity [anf, cf] procs

@[breakpoint] meta def driver
  (externs : list extern_fn)
  (procs : list procedure) : ir_compiler (list ir.item × list error) := do
  trace_ir "driver",
  map <- arities,
  procs' ← apply_pre_ir_passes procs <$> configuration <*> pure map,
  (defns, errs) ← sequence_err (compile_defns procs'),
  (decls, errs) ← sequence_err (compile_decls externs),
  main ← emit_main procs',
  return (ir.item.defn main :: defns ++ decls, errs)

meta def make_list (type : expr) : list expr → tactic expr
| [] := mk_mapp `list.nil [some type]
| (e :: es) := do
  tail <- make_list es,
  mk_mapp `list.cons [some type, some e, some tail]

meta def get_attribute_body (attr : name) (type : expr) : tactic expr := do
  tactic.trace attr,
  decl <- get_decl attr,
  -- add type checking in here ...
  match decl with
  | (declaration.defn _ _ _ body _ _) := pure body
  | _ := fail "NYI"
  end

meta def get_attribute_bodies (attr : name) (type : expr) : tactic expr := do
  names <- attribute.get_instances attr,
  bodies <- monad.for names (fun n, get_attribute_body n type),
  make_list type bodies

meta def get_ir_decls : tactic expr := do
  ty <- mk_const `ir.decl,
  get_attribute_bodies `ir_decl ty

meta def get_ir_defns : tactic expr := do
  ty <- mk_const `ir.defn,
  get_attribute_bodies `ir_def ty

meta def run_ir {A : Type} (action : ir_compiler A) (inital : ir_compiler_state): result error A :=
  prod.fst $ run action inital

meta def compile'
  (conf : config)
  (extern_fns : list extern_fn)
  (procs : list procedure)
  (ctxt : ir.context) : format := do
    let arity := mk_arity_map procs in
    let action : ir_compiler _ := driver extern_fns procs in
    match (run_ir action (ctxt, conf, arity, 0)) with
    | result.err e := error.to_string e
    | result.ok (items, errs) :=
      if list.length errs = 0
      then (format_cpp.program items)
      else (format_error (error.many errs))
    end

@[breakpoint] meta def compile
  (conf : config)
  (extern_fns : list extern_fn)
  (procs : list procedure) : tactic format := do
    decls_list_expr <- get_ir_decls,
    defns_list_expr <- get_ir_defns,
    decls <- eval_expr (list ir.decl) decls_list_expr,
    defns <- eval_expr (list ir.defn) defns_list_expr,
    let ctxt := ir.new_context decls defns in
    pure $ compile' conf extern_fns procs ctxt

end native
