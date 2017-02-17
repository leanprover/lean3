/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.meta.format
import init.meta.expr
import init.category.state
import init.data.string
import init.data.list.instances

import tools.native.ir
import tools.native.ir.compiler
import tools.native.format
import tools.native.internal
import tools.native.anf
import tools.native.cf
-- import tools.native.lift_switch
import tools.native.pass
import tools.native.util
import tools.native.config
import tools.native.result
import tools.native.attributes

-- import init.debugger
-- import init.debugger.cli
-- set_option debugger true

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

meta def in_lean_ns (n : name) : ir.symbol :=
  ir.symbol.external (some `lean) n

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

meta def mk_error {T} (msg : string) : ir_compiler T :=
  trace ("ERROR: " ++ msg) (lift_result (native.result.err $ error.string msg))

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

meta def fresh_symbol : ir_compiler ir.symbol :=
  fmap ir.symbol.name fresh_name

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
--     forall A (xs : list A),
--     list.length (label xs) = list.length xs :=
--  begin
--    intros,
--    induction xs,
--    unfold label,
--    simp,
--  end

-- HELPERS --
meta def assert_name : ir.expr → ir_compiler ir.symbol
| (ir.expr.sym s) := lift_result $ native.result.ok s
| e := mk_error $ "expected name found: " ++ to_string (format_cpp.expr e)

meta def assert_expr : ir.stmt → ir_compiler ir.expr
| (ir.stmt.e exp) := return exp
| s := mk_error ("internal invariant violated, found: " ++ to_string (format_cpp.stmt s))

meta def mk_ir_call (head : ir.symbol) (args : list ir.expr) : ir_compiler ir.expr :=
  let args'' := list.map assert_name args
  in do
    args' ← monad.sequence args'',
    return (ir.expr.call head args')

meta def mk_direct_call (head : ir.symbol) (args : list ir.expr) : ir_compiler ir.stmt := do
  if list.length args < 9
  then ir.stmt.e <$> (mk_ir_call head args)
  else match head with
       | (ir.symbol.name n) := ir.stmt.e <$> mk_ir_call head args
       | (ir.symbol.external ns n) := do
          array <- fresh_name,
          idx <- fresh_name,
          args' <- monad.mapm assert_name args,
          pure $ ir.stmt.letb array (ir.ty.array (ir.ty.symbol (in_lean_ns `vm_obj))) (ir.expr.array args')
          (ir.stmt.letb idx ir.base_type.unsigned (ir.expr.raw_int $ list.length args)
          (ir.stmt.e (ir.expr.call head [idx, array])))
       end

meta def mk_nargs_symbol : ir.symbol -> ir.symbol
| (ir.symbol.name n) := ir.symbol.name (n ++ "nargs")
| o := o

meta def mk_under_sat_call (head : ir.symbol) (arity : nat) (args : list ir.expr) : ir_compiler ir.expr :=
let args'' := list.map assert_name args in do
    args' ← monad.sequence args'',
    if arity < 9
    then return (ir.expr.mk_native_closure head arity args')
    else return (ir.expr.mk_native_closure (mk_nargs_symbol head) arity args')

meta def bind_value_with_ty (val : ir.expr) (ty : ir.ty) (body : ir.symbol → ir_compiler ir.stmt) : ir_compiler ir.stmt := do
  fresh ← fresh_symbol,
  ir.stmt.letb fresh ty val <$> (body fresh)

meta def bind_value (val : ir.expr) (body : ir.symbol → ir_compiler ir.stmt) : ir_compiler ir.stmt :=
  bind_value_with_ty val (ir.ty.object none) body

-- not in love with this --solution-- hack, revisit
meta def compile_local (n : ir.symbol) : ir_compiler ir.symbol :=
  return n
-- return $ (mk_str_name "_$local$_" (name.to_string_with_sep "_" n))

meta def mk_invoke (loc : ir.symbol) (args : list ir.expr) : ir_compiler ir.stmt := do
  args' <- monad.mapm assert_name args,
  loc' ← compile_local loc,
  if args'^.length < 9
  then return (ir.stmt.e $ ir.expr.invoke loc' args')
  else do
    array <- fresh_name,
    idx <- fresh_name,
    args' <- monad.mapm assert_name args,
    pure $ ir.stmt.letb array (ir.ty.array (ir.ty.symbol (in_lean_ns `vm_obj))) (ir.expr.array args')
      (ir.stmt.letb idx ir.base_type.unsigned (ir.expr.raw_int $ list.length args)
        (ir.stmt.e (ir.expr.invoke loc [idx, array])))

meta def mk_over_sat_call (head : ir.symbol) (fst snd : list ir.expr) : ir_compiler ir.stmt :=
let fst' := list.map assert_name fst,
    snd' := list.map assert_name snd in do
  args' ← monad.sequence fst',
  args'' ← monad.sequence snd',
  fresh ← fresh_symbol,
  locl ← compile_local fresh,
  invoke ← mk_invoke fresh (ir.expr.sym <$> args''),
  return $ (ir.stmt.seq [
    ir.stmt.letb locl (ir.ty.object none) (ir.expr.call head args') ir.stmt.nop,
    invoke
  ])

-- meta def is_return (n : name) : bool :=
-- `native_compiler.return = n

meta def compile_call (head : ir.symbol) (arity : nat) (args : list ir.expr) : ir_compiler ir.stmt := do
  -- trace_ir $ "compile_call: " ++ (to_string head),
  if list.length args = arity
  then mk_direct_call head args
  else if list.length args < arity
  then ir.stmt.e <$> mk_under_sat_call head arity args
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

meta def one_or_error_message (msg : string) (args : list expr) : ir_compiler expr :=
match args with
| ((h : expr) :: []) := lift_result $ native.result.ok h
| _ := mk_error $ "internal invariant violated: " ++ msg ++ " should only have one argument"
end

meta def panic (msg : string) : ir_compiler ir.expr :=
  return $ ir.expr.panic msg

-- END HELPERS --

meta def bind_case_fields' (scrut : ir.symbol) : list (nat × ir.symbol) → ir.stmt → ir_compiler ir.stmt
| [] body := return body
| ((n, f) :: fs) body := do
  loc ← compile_local f,
  ir.stmt.letb loc (ir.ty.object none) (ir.expr.project scrut n) <$> (bind_case_fields' fs body)

meta def bind_case_fields (scrut : ir.symbol) (fs : list ir.symbol) (body : ir.stmt) : ir_compiler ir.stmt :=
  bind_case_fields' scrut (label fs) body

meta def mk_is_simple (scrut : ir.symbol) : ir.expr :=
  ir.expr.call (ir.symbol.external none `is_simple) [scrut]

meta def mk_is_zero (n : ir.symbol) : ir.expr :=
  ir.expr.equals (ir.expr.raw_int 0) (ir.expr.sym n)

meta def mk_cidx (obj : ir.symbol) : ir.expr :=
  ir.expr.call (ir.symbol.external none `cidx) [obj]

meta def mk_cases_on (case_name scrut : ir.symbol) (cases : list (nat × ir.stmt)) (default : ir.stmt) : ir_compiler ir.stmt := do
  ctor_index <- fresh_symbol,
  pure $ ir.stmt.seq [
   ir.stmt.letb ctor_index (ir.ty.name `unsigned) (mk_cidx scrut) ir.stmt.nop,
   ir.stmt.switch ctor_index cases default
  ]

meta def compile_cases (action : expr → ir_compiler ir.stmt) (scrut : ir.symbol)
: list (nat × expr) → ir_compiler (list (nat × ir.stmt))
| [] := return []
| ((n, body) :: cs) := do
  (fs, body') ← take_arguments body,
  body'' ← action body',
  cs' ← compile_cases cs,
  case ← bind_case_fields scrut (list.map ir.symbol.name fs) body'',
  return $ (n, case) :: cs'

meta def compile_cases_on_to_ir_stmt
    (case_name : ir.symbol)
    (cases : list expr)
    (action : expr → ir_compiler ir.stmt) : ir_compiler ir.stmt := do
    default ← panic "default case should never be reached",
    match cases with
    | [] := mk_error $ "found " ++ to_string case_name ++ " applied to zero arguments"
    | (h :: cs) := do
      ir_scrut ← action h >>= assert_expr,
      bind_value ir_scrut (fun scrut, do
        cs' ← compile_cases action scrut (label cs),
        mk_cases_on case_name scrut cs' (ir.stmt.e default))
    end

meta def bind_builtin_case_fields' (scrut : ir.symbol) : list (nat × ir.symbol) → ir.stmt → ir_compiler ir.stmt
| [] body := return body
| ((n, f) :: fs) body := do
  loc ← compile_local f,
  idx <- fresh_name,
  kont <- bind_builtin_case_fields' fs body,
  pure $ ir.stmt.letb idx ir.ty.int (ir.expr.raw_int n) (
  ir.stmt.letb loc (ir.ty.object none) (ir.expr.call `index [scrut, idx]) kont)

meta def bind_builtin_case_fields (scrut : ir.symbol) (fs : list ir.symbol) (body : ir.stmt) : ir_compiler ir.stmt :=
  bind_builtin_case_fields' scrut (label fs) body

meta def compile_builtin_cases (action : expr → ir_compiler ir.stmt) (scrut : ir.symbol)
  : list (nat × expr) → ir_compiler (list (nat × ir.stmt))
| [] := return []
| ((n, body) :: cs) := do
  (fs, body') ← take_arguments body,
  body'' ← action body',
  cs' ← compile_builtin_cases cs,
  -- TODO: remove hardwired name here
  case ← bind_builtin_case_fields `buffer (list.map ir.symbol.name fs) body'',
  return $ (n, case) :: cs'

meta def mk_builtin_cases_on (case_name : name) (scrut : ir.symbol) (cases : list (nat × ir.stmt)) (default : ir.stmt) : ir.stmt :=
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

-- we should add applicative brackets
meta def mk_simple_nat_cases_on (scrut : ir.symbol) (zero_case succ_case : ir.stmt) : ir_compiler ir.stmt :=
  bind_value_with_ty (mk_cidx scrut) (ir.ty.name `int) (fun cidx,
    bind_value_with_ty (mk_is_zero cidx) (ir.ty.name `bool) (fun is_zero,
    pure $ ir.stmt.ite is_zero zero_case succ_case))

meta def mk_mpz_nat_cases_on (scrut : ir.symbol) (zero_case succ_case : ir.stmt) : ir_compiler ir.stmt :=
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

meta def mk_nat_cases_on (scrut : ir.symbol) (zero_case succ_case : ir.stmt) : ir_compiler ir.stmt :=
  bind_value_with_ty (mk_is_simple scrut) (ir.ty.name `bool) (fun is_simple,
    ir.stmt.ite is_simple <$>
      mk_simple_nat_cases_on scrut zero_case succ_case <*>
      mk_mpz_nat_cases_on scrut zero_case succ_case)

meta def assert_two_cases (cases : list expr) : ir_compiler (expr × expr) :=
  match cases with
  | c1 :: c2 :: _ := return (c1, c2)
  | _ := mk_error "nat.cases_on should have exactly two cases"
  end

meta def mk_vm_nat (n : ir.symbol) : ir.expr :=
  ir.expr.call (in_lean_ns `mk_vm_simple) [n]

meta def compile_succ_case (action : expr → ir_compiler ir.stmt) (scrut : ir.symbol) (succ_case : expr) : ir_compiler ir.stmt := do
  (fs, body') ← take_arguments succ_case,
  body'' ← action body',
  match fs with
  | pred :: _ := do
    loc ← compile_local pred,
    fresh ← fresh_name,
    bind_value_with_ty (mk_cidx scrut) (ir.ty.name `int) (fun cidx,
      bind_value_with_ty (ir.expr.sub (ir.expr.sym cidx) (ir.expr.raw_int 1)) (ir.ty.name `int) (fun sub,
      pure $ ir.stmt.letb loc (ir.ty.object none) (mk_vm_nat sub) body''
    ))
  | _ := mk_error "compile_succ_case too many fields"
  end

meta def compile_nat_cases_on_to_ir_expr
(case_name : ir.symbol)
(cases : list expr)
(action : expr → ir_compiler ir.stmt) : ir_compiler ir.stmt :=
  match cases with
  | [] := mk_error $ "found " ++ to_string case_name ++ " applied to zero arguments"
  | (h :: cs) := do
    ir_scrut ← action h >>= assert_expr,
    (zero_case, succ_case) ← assert_two_cases cs,
    -- trace_ir (to_string zero_case),
    -- trace_ir (to_string succ_case),
    bind_value ir_scrut (fun scrut, do
      zc ← action zero_case,
      sc ← compile_succ_case action scrut succ_case,
      mk_nat_cases_on scrut zc sc
    )
  end

def last {A : Type} : list A -> option A
| [] := none
| (x :: []) := some x
| (_ :: xs) := last xs

-- I had to manually transform this code due to issues with the equation compiler
-- set_option trace.eqn_compiler.elim_match true
-- why doesn't matching on the option work here
meta def assign_last_expr_list
  (result_var : ir.symbol)
  (rec : ir.stmt -> ir_compiler ir.stmt)
  (ss : list ir.stmt) : ir_compiler ir.stmt :=
  option.cases_on (last ss)
    (mk_error "internal invariant")
   (fun s, do
    s' <- rec s,
    pure $ ir.stmt.seq $ list.append (list.taken (list.length ss - 1) ss) [s'])

meta def assign_last_expr_cases (result_var : ir.symbol) (action : ir.stmt -> ir_compiler ir.stmt) :
  list (prod nat ir.stmt) -> ir_compiler (list (prod nat ir.stmt))
| [] := pure []
| ((n, c) :: cs) := do
  c' <- action c,
  cs' <- assign_last_expr_cases cs,
  pure $ (n, c') :: cs'

meta def assign_last_expr (result_var : ir.symbol) : ir.stmt -> ir_compiler ir.stmt
| (ir.stmt.seq ss) := assign_last_expr_list result_var assign_last_expr ss
| (ir.stmt.ite c tb fb) := ir.stmt.ite c <$> assign_last_expr tb <*> assign_last_expr fb
| (ir.stmt.switch scrut cases default) :=
  ir.stmt.switch scrut <$> assign_last_expr_cases result_var assign_last_expr cases <*> pure default
| (ir.stmt.letb n ty val body) := ir.stmt.letb n ty val <$> assign_last_expr body
| (ir.stmt.e e) := pure $ ir.stmt.assign result_var e
| (ir.stmt.assign _ _) := mk_error "UNSUUPORTED assign"
| (ir.stmt.return _) := mk_error "UNSUUPORTED return"
| (ir.stmt.nop) := pure $ ir.stmt.nop

-- meta def assert_is_switch : ir_compiler
meta def compile_native_assign (n v body : expr) (action : expr -> ir_compiler ir.stmt) : ir_compiler ir.stmt := do
  n' <- action n,
  e <- assert_expr n',
  nm <- assert_name e,
  v' <- action v,
  v'' <- assign_last_expr nm v',
  body' <- action body,
  return $ ir.stmt.letb nm (ir.ty.object none) ir.expr.uninitialized (ir.stmt.seq [v'', body'])

meta def macro_get_name : expr -> name
| (expr.macro mdef _ _) := expr.macro_def_name mdef
| _ := name.anonymous

meta def compile_return : ir.stmt -> ir_compiler ir.stmt
| (ir.stmt.letb nm ty val body) :=
  ir.stmt.letb nm ty val <$> compile_return body
| s := do
  e <- assert_expr s,
  pure $ ir.stmt.return e

meta def compile_const_head_expr_app_to_ir_stmt
  (head : expr)
  (args : list expr)
  (action : expr → ir_compiler ir.stmt) : ir_compiler ir.stmt := do
  -- trace_ir ("HEAD:" ++ to_string head),
  match app_kind head with
  | application_kind.return := do
    rexp ← one_or_error args,
    rexp' <- action rexp,
    compile_return rexp'
  | application_kind.nat_cases :=
    compile_nat_cases_on_to_ir_expr (expr.const_name head) args action
  | application_kind.projection n := do
      obj <- one_or_error_message "projection" args,
      ir_obj <- action obj,
      e <- assert_expr ir_obj,
      nm <- assert_name e,
      pure $ ir.stmt.e $ ir.expr.project nm n
  | application_kind.constructor n := do
    args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
    ir.stmt.e <$> mk_object (unsigned.of_nat n) args'
  | application_kind.cases :=
    -- hack, clean this up
    match get_builtin (expr.const_name head) with
    | option.some (builtin.cases _ _) :=
      compile_builtin_cases_on_to_ir_expr (expr.const_name head) args action
    | _ := compile_cases_on_to_ir_stmt (expr.const_name head) args action
    end
  | application_kind.assign := do
    match args with
    | (n :: v :: body :: []) :=
      match v with
      | (expr.macro mdef arg_count args) :=
        match native.get_quote_expr (expr.macro mdef arg_count args) with
        | option.some _ := do
          fresh <- fresh_name,
          st <- action n,
          e <- assert_expr st,
          nm <- assert_name e,
          body' <- action body,
          pure $ (ir.stmt.letb fresh ir.base_type.str (ir.expr.lit $ ir.literal.binary (native.serialize_quote_macro v)) $
                  ir.stmt.letb nm (ir.ty.object none) (ir.expr.call (in_lean_ns `deserialize_quoted_expr) [fresh]) body')

        | option.none := mk_error $ "unsupported macro: " ++ to_string (macro_get_name v)
        end
      | _ := compile_native_assign n v body action
      end
    | _ := mk_error "ERROR"
    end
  | _ :=
    match get_builtin (expr.const_name head) with
    | option.some builtin :=
      match builtin with
      | builtin.vm n := mk_error "vm"
      | builtin.cfun n arity := do
        args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
        compile_call (in_lean_ns n) arity args'
      | builtin.cases n arity :=
        compile_builtin_cases_on_to_ir_expr (expr.const_name head) args action
      end
    | option.none := do
      args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
      arity ← lookup_arity (expr.const_name head),
      compile_call (expr.const_name head) arity args'
  end
end

meta def compile_expr_app_to_ir_stmt
  (head : expr)
  (args : list expr)
  (action : expr → ir_compiler ir.stmt) : ir_compiler ir.stmt := do
    -- trace_ir (to_string head  ++ to_string args),
    if expr.is_constant head = bool.tt
    then compile_const_head_expr_app_to_ir_stmt head args action
    else if expr.is_local_constant head
    then do
      args' ← monad.mapm (fun x, action x >>= assert_expr) args,
      mk_invoke (expr.local_uniq_name head) args'
    else (mk_error ("unsupported call position" ++ (to_string head)))

meta def compile_expr_macro_to_ir_expr (e : expr) (action : expr -> ir_compiler ir.stmt) : ir_compiler ir.stmt :=
  match native.get_nat_value e with
  | option.some n := ir.stmt.e <$> mk_nat_literal n
  | option.none :=
    match native.get_quote_expr e with
    | option.some _ := do
      fresh <- fresh_name,
      pure $ ir.stmt.letb fresh ir.base_type.str (ir.expr.lit $ ir.literal.string (native.serialize_quote_macro e)) ir.stmt.nop
    | option.none := mk_error $ "unsupported macro: " ++ to_string (macro_get_name e)
    end
  end

meta def assign_stmt' (n : ir.symbol) : ir.stmt → ir_compiler ir.stmt
| (ir.stmt.e e) := do
  pure $ ir.stmt.assign n e
| s := pure s

meta def assign_stmt (n : ir.symbol) (stmt : ir.stmt) : ir_compiler ir.stmt := do
  n' <- compile_local n,
  st <- assign_stmt' n' stmt,
  pure $ ir.stmt.letb n' (ir.ty.object none) ir.expr.uninitialized st

-- open application_kk
meta def compile_expr_to_ir_stmt : expr → ir_compiler ir.stmt
| (expr.const n ls) := do
  -- trace_ir ("const: " ++ to_string n),
  match native.is_internal_cnstr (expr.const n ls) with
  | option.none :=
    -- TODO, do I need to case on arity here? I should probably always emit a call
    match get_builtin n with
    | option.some (builtin.cfun n' arity) :=
      compile_call (in_lean_ns n') arity []
    | _ :=
      if n = "_neutral_"
      then (pure $ ir.stmt.e $ ir.expr.mk_object 0 [])
      else (if is_unreachable n
      then (pure $ ir.stmt.e $ ir.expr.unreachable)
      else do
        arity ← lookup_arity n,
        compile_call n arity [])
    end
  | option.some arity := pure $ ir.stmt.e $ ir.expr.mk_object (unsigned.to_nat arity) []
  end
| (expr.var i) := mk_error "there should be no bound variables in compiled terms"
| (expr.sort _) := mk_error "found sort"
| (expr.mvar _ _) := mk_error "unexpected meta-variable in expr"
| (expr.local_const n _ _ _) := ir.stmt.e <$> (ir.expr.sym <$> compile_local n)
| (expr.app f x) :=
  let head := expr.get_app_fn (expr.app f x),
      args := expr.get_app_args (expr.app f x)
  in compile_expr_app_to_ir_stmt head args compile_expr_to_ir_stmt
| (expr.lam _ _ _ _) := mk_error "found lam"
| (expr.pi _ _ _ _) := mk_error "found pi, should not be translating a Pi for any reason (yet ...)"
| (expr.macro d sz args) := compile_expr_macro_to_ir_expr (expr.macro d sz args) compile_expr_to_ir_stmt
| (expr.elet n _ v body) := do
  n' ← compile_local n,
  v' ← compile_expr_to_ir_stmt v,
  assign <- assign_stmt n v',
  body' ← compile_expr_to_ir_stmt (expr.instantiate_var body (mk_local n)),
  return $ ir.stmt.seq [assign, body']

meta def compile_defn_to_ir (decl_name : name) (params : list name) (body : expr) : ir_compiler ir.defn := do
  body' ← compile_expr_to_ir_stmt body,
  let no_params := list.length params,
      const_obj_ref := ir.ty.ref (ir.ty.object none),
      param_tys := list.repeat const_obj_ref no_params,
      params := (list.zip params param_tys)
  in pure (ir.defn.mk bool.tt decl_name params (ir.ty.object none) body')

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
  -- trace ("compiling: " ++ to_string decl_name) (fun u, do
  refinement <- has_ir_refinement decl_name,
  match refinement with
  | some item :=
    match item with
    | ir.item.defn d := pure d
    | _ := mk_error "not sure what to do here yet"
    end
  | none := do
    (args, body) ← take_arguments e,
    -- do trace_ir (to_string e),
    compile_defn_to_ir (replace_main decl_name) args body
  end

meta def bind_args (array : ir.symbol) (n : nat) : ir_compiler (list ir.symbol × ir.stmt) :=
  nat.repeat (fun n r, do
    (ns, body) <- r,
    fresh <- fresh_name,
    fresh2 <- fresh_name,
    pure $ (fresh2 :: ns, ir.stmt.letb fresh ir.ty.int (ir.expr.raw_int n) (
    ir.stmt.letb fresh2 (ir.ty.object none) (ir.expr.call `index [array, fresh]) body))) n (pure ([], ir.stmt.nop))

meta def compile_nargs_body (decl_name array : name) (arity : nat) : ir_compiler ir.stmt := do
  (ns, s) <- bind_args array arity,
  pure $ ir.stmt.seq [s, ir.stmt.return $ ir.expr.call decl_name (list.reverse ns)]

meta def compile_defn_nargs (decl_name : name) (e : expr) : ir_compiler ir.defn := do
  fresh1 <- fresh_name,
  fresh2 <- fresh_name,
  ir.defn.mk bool.tt
    (name.mk_string "nargs" decl_name)
    [(fresh1, ir.base_type.unsigned), (fresh2, ir.ty.raw_ptr $ ir.ty.symbol (in_lean_ns `vm_obj))] (ir.ty.object none)
    <$> (compile_nargs_body decl_name fresh2 (native.get_arity e))
  -- refinement <- has_ir_refinement decl_name,
  -- match refinement with
  -- | some item :=
  --   match item with
  --   | ir.item.defn d := pure d
  --   | _ := mk_error "not sure what to do here yet"
  --   end
  -- | none :=
  --   let arity := native.get_arity e in do (args, body) ← take_arguments e,
  --   do trace_ir (to_string e),
  --   compile_defn_to_ir (replace_main decl_name) args body
  -- end

meta def compile_defn_to_items (decl_name : name) (e : expr) : list (ir_compiler ir.item) :=
  let default := [ir.item.defn <$> compile_defn decl_name e]
  in if native.get_arity e < 9
     then default
     else default ++ [ir.item.defn <$> compile_defn_nargs decl_name e]

meta def compile_defns : list procedure → list (ir_compiler ir.item) :=
  fun ps, list.bind ps (fun p, compile_defn_to_items (prod.fst p) (prod.snd p))

meta def mk_builtin_cases_on_proto (n : name) : ir_compiler ir.decl := do
  o <- fresh_name,
  data <- fresh_name,
  return $ ir.decl.mk n [(o, ir.ty.ref (ir.ty.object none)), (data, ir.ty.mut_ref ir.ty.object_buffer)] (ir.ty.name `unsigned)

meta def n_fresh : nat -> ir_compiler (list name)
| 0 := return []
| (nat.succ n) := do
   fs <- n_fresh n,
   f <- fresh_name,
   return (f :: fs)

meta def compile_decl : extern_fn → ir_compiler ir.item
| (| _, lean_name, native_name, arity |) :=
  if is_cases_on (expr.const lean_name [])
  then ir.item.decl <$> mk_builtin_cases_on_proto native_name
  else
  if (unsigned.to_nat arity) < 9
  then do
    args <- n_fresh (unsigned.to_nat arity),
    types <- pure $ list.repeat (ir.ty.ref $ ir.ty.object none) (unsigned.to_nat arity),
    -- this is a temp. hack
    return $ ir.item.decl $ ir.decl.mk native_name (list.zip args types) (ir.ty.object none)
  else do
    args <- n_fresh 2,
    return $ ir.item.decl $ ir.decl.mk native_name (list.zip args [ir.base_type.unsigned, ir.ty.raw_ptr $ ir.ty.symbol (in_lean_ns `vm_obj)]) (ir.ty.object none)

meta def compile_decls : list extern_fn → list (ir_compiler ir.item) :=
  fun xs, list.map compile_decl xs

meta def format_error : error → format
| (error.string s) := to_fmt s
| (error.many es) := format_concat (list.map format_error es)

-- Not sure if this is a good idea.
meta instance has_coe_lift_list (A B : Type) [elem_coe : has_coe A B] : has_coe (list A) (list B) :=
  (| list.map (@has_coe.coe A B elem_coe) |)

meta def mk_lean_name (n : name) : ir.expr :=
  ir.expr.constructor (in_lean_ns `name) (name.components n)

meta def emit_declare_vm_builtin_nargs (n : name) (body : expr) : ir_compiler ir.stmt := do
  vm_name ←  pure $ (mk_lean_name n),
  fresh ← fresh_name,
  arityName ← fresh_name,
  arity ← pure $ (ir.expr.lit $ ir.literal.integer (get_arity body)),
  let cpp_name := in_lean_ns `name,
    single_binding :=
      (ir.stmt.letb fresh (ir.ty.symbol cpp_name) vm_name (
       ir.stmt.letb arityName (ir.base_type.unsigned) arity (
        ir.stmt.assign `env (ir.expr.call (in_lean_ns `add_native) [`env, fresh, arityName, replace_main (n ++ "nargs")]))))
  in return single_binding

meta def emit_declare_vm_builtin (n : name) (body : expr) : ir_compiler ir.stmt := do
  vm_name ← pure $ (mk_lean_name n),
  fresh ← fresh_name,
  let cpp_name := in_lean_ns `name,
    single_binding :=
    (ir.stmt.letb fresh (ir.ty.symbol cpp_name) vm_name (
      ir.stmt.assign `env (ir.expr.call (in_lean_ns `add_native) [`env, fresh, replace_main n])))
  in return $ single_binding

meta def emit_declare_vm_builtins : list (name × expr) → ir_compiler (list ir.stmt)
| [] := return []
| ((n, body) :: es) := do
  tail ← emit_declare_vm_builtins es,
  if get_arity body < 9
  then do b <- emit_declare_vm_builtin n body, return (b :: tail)
  else do b <- emit_declare_vm_builtin_nargs n body, return (b :: tail)

meta def emit_main (procs : list (name × expr)) : ir_compiler ir.defn := do
  builtins ← emit_declare_vm_builtins procs,
  arity ← lookup_arity `main,
  vm_simple_obj ← fresh_name,
  call_main ← compile_call "___lean__main" arity [ir.expr.sym vm_simple_obj],
  return (ir.defn.mk bool.tt `main [] ir.ty.int $ ir.stmt.seq ([
    ir.stmt.e $ ir.expr.call (in_lean_ns `initialize) [],
    ir.stmt.letb `env (ir.ty.symbol (in_lean_ns `environment)) ir.expr.uninitialized ir.stmt.nop
  ] ++ builtins ++ [
    ir.stmt.letb `ios (ir.ty.symbol (in_lean_ns `io_state)) (ir.expr.call (in_lean_ns `get_global_ios) []) ir.stmt.nop,
    ir.stmt.letb `opts (ir.ty.symbol (in_lean_ns `options)) (ir.expr.call (in_lean_ns `get_options_from_ios) [`ios]) ir.stmt.nop,
    ir.stmt.letb `S (ir.ty.symbol (in_lean_ns `vm_state)) (ir.expr.constructor (in_lean_ns `vm_state) [`env, `opts]) ir.stmt.nop,
    ir.stmt.letb `scoped (ir.ty.symbol (in_lean_ns `scope_vm_state)) (ir.expr.constructor (in_lean_ns `scope_vm_state) [`S]) ir.stmt.nop,
    ir.stmt.assign `g_env (ir.expr.address_of `env),
    ir.stmt.letb vm_simple_obj (ir.ty.object none) (ir.expr.mk_object 0 []) ir.stmt.nop,
    call_main
]))

meta def name_to_str_array (n : name) : ir.literal :=
    ir.literal.array $ list.map (fun n', ir.literal.string $ to_string n') $ name.components n

meta def mk_let_native_symbol_name (n : name) : ir_compiler (name × ir.stmt) := do
  fresh <- fresh_name,
  return $ (fresh, ir.stmt.letb fresh (ir.ty.symbol $ in_lean_ns `name) (ir.expr.lit $ name_to_str_array n) ir.stmt.nop)

meta def emit_native_symbol_pairs (procs : list (name × expr)) : ir_compiler ir.stmt :=
  let ns := list.map prod.fst procs,
      oleans := (list.repeat (ir.literal.string "") (list.length ns)),
      syms := list.map (fun n, ir.literal.string $ format_cpp.mangle_symbol n) ns,
      arities := list.map (fun p , ir.literal.integer $ get_arity (prod.snd p)) procs
  in do
    -- not sure why this unification problem fails
    (names, lets) <- list.unzip <$> (@monad.mapm ir_compiler _ _ _ mk_let_native_symbol_name ns),
    let both := (list.zip oleans (list.zip names (list.zip syms arities))) in
    pure (ir.stmt.seq
    (lets ++ [(ir.stmt.return $ ir.expr.lit $ ir.literal.array ((flip list.map both) (fun (| o, n, s, a |), ir.literal.array [o, ir.literal.symbol n, s, a])))]))

meta def emit_package_initialize (procs : list (name × expr)) : ir_compiler ir.defn :=
  ir.defn.mk bool.tt `initialize [] (ir.ty.symbol (in_lean_ns `native_symbol_seq)) <$>
     emit_native_symbol_pairs procs

meta def apply_pre_ir_passes
  (procs : list procedure)
  (conf : config)
  (arity : arity_map) : list procedure :=
  run_passes conf arity [anf, cf] procs

meta def driver
  (externs : list extern_fn)
  (procs : list procedure) : ir_compiler (list ir.item × list error) := do
  conf <- configuration,
  map <- arities,
  procs' ← apply_pre_ir_passes procs <$> configuration <*> pure map,
  (defns, defn_errs) ← sequence_err (compile_defns procs'),
  (decls, decl_errs) ← sequence_err (compile_decls externs),
  if is_executable conf
  then do
    main ← emit_main procs',
    return (ir.item.defn main :: defns ++ decls, defn_errs ++ decl_errs)
  else do
    init <- emit_package_initialize procs',
  return (ir.item.defn init :: defns ++ decls, defn_errs ++ decl_errs)

meta def make_list (type : expr) : list expr → tactic expr
| [] := mk_mapp `list.nil [some type]
| (e :: es) := do
  tail <- make_list es,
  mk_mapp `list.cons [some type, some e, some tail]

meta def get_attribute_body (attr : name) (type : expr) : tactic expr := do
  -- tactic.trace attr,
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

meta def merge {K V : Type} (map map' : rb_map K V) : rb_map K V :=
   rb_map.fold map' map (fun key data m, rb_map.insert m key data)

meta def extend_with_list {K V : Type} [has_ordering K] (map : rb_map K V) (es : list (prod K V)) : rb_map K V :=
   merge map (rb_map.of_list es)

meta def extern_to_arities : extern_fn -> prod name nat
| (| _, lean_name, _, arity |) := (lean_name, unsigned.to_nat arity)

meta def compile'
  (conf : config)
  (extern_fns : list extern_fn)
  (procs : list procedure)
  (ctxt : ir.context) : result error format := do
    let arity := extend_with_list (mk_arity_map procs) (list.map extern_to_arities extern_fns) in
    let action : ir_compiler _ := driver extern_fns procs in
    match (run_ir action (ctxt, conf, arity, 0)) with
    | result.err e := result.err e
    | result.ok (items, errs) :=
      if list.length errs = 0
      then pure (format_cpp.program items)
      else result.err (error.many errs)
  end

meta def compile
  (conf : config)
  (extern_fns : list extern_fn)
  (procs : list procedure) : tactic format := do
    tactic.trace "starting to execute the Lean compiler",
    decls_list_expr <- get_ir_decls,
    defns_list_expr <- get_ir_defns,
    decls <- eval_expr (list ir.decl) decls_list_expr,
    defns <- eval_expr (list ir.defn) defns_list_expr,
    let ctxt := ir.new_context decls defns in
    match compile' conf extern_fns procs ctxt with
    | result.err e := tactic.fail $ error.to_string e
    | result.ok format := pure format
    end

end native
