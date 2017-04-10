-- declare_trace smt2
import system.io
import system.process
import .solvers.z3
import .syntax
import .builder
import .tactic
import .attributes

open tactic
open smt2
open smt2.builder

meta structure smt2_state : Type :=
(sort_map : rb_map expr unit)

meta def smt2_state.initial : smt2_state :=
⟨ rb_map.mk _ _ ⟩

@[reducible] meta def smt2_m (α : Type) :=
state_t smt2_state tactic α

meta instance tactic_to_smt2_m (α : Type) : has_coe (tactic α) (smt2_m α) :=
⟨ fun tc, fun s, do res ← tc, return (res, s) ⟩

meta def mangle_name (n : name) : string :=
"lean_" ++ n^.to_string_with_sep "-"

meta def ensure_sort (sort : expr) : smt2_m unit :=
do st ← state_t.read,
   match st.sort_map.find sort with
   | some _ := return ()
   | none :=
     state_t.write (⟨ st.sort_map.insert sort () ⟩)
   end

inductive formula_type
| const : name → smt2.sort → formula_type
| fn : name → list smt2.sort → smt2.sort → formula_type
| prop_formula
| unsupported

-- FIXME
meta def fn_type : expr → (list expr × expr)
| (expr.pi _ _ ty rest) :=
    let (args, rt) := fn_type rest
    in (ty :: args, rt)
| rt := ([], rt)

meta def type_to_sort (e : expr) : tactic smt2.sort :=
if (e = ```(int))
then return $ "Int"
else if (e = ```(Prop))
then return $ "Bool"
else if e.is_local_constant
then return $ (mangle_name e.local_uniq_name)
else tactic.fail "unsupported type"

meta def formula_type_from_arrow (n : name) (e : expr) : tactic formula_type :=
do ty ← infer_type e,
   let (arg_tys, ret_ty) := fn_type ty
   in formula_type.fn n <$> (monad.mapm type_to_sort arg_tys) <*> (type_to_sort ret_ty)

/-- The goal of this function is to categorize the set of formulas in the hypotheses,
    and goal. We want to narrow down from the full term language of Lean to a fragment
    of formula's we suppose. The below code makes some assumptions:

   A local constant of the form `(P : Prop)`, must be reflected as declaration
   in SMT2 that is `(declare-const P Bool)`.

   An occurence of a proof of `P`, `(p : P)`, must be transformed into
   `(assert P)`. If P is a formula, not an atom, we must transform P into a corresponding
   SMT2 formula and `(assert P)`.
-/
meta def classify_formula (e : expr) : tactic formula_type :=
do ty ← infer_type e,
   prop_sorted ← is_prop ty,
   if e.is_local_constant
   then if (ty = ```(Prop))
        then return $ formula_type.const (e.local_uniq_name) "Bool"
        else if (ty = ```(int))
        then return $ formula_type.const (e.local_uniq_name) "Int"
        else if ty.is_arrow
        then formula_type_from_arrow (e.local_uniq_name) e
        else if prop_sorted
        then return formula_type.prop_formula
        else return formula_type.unsupported
   else if e.is_constant
   then if (ty = ```(Prop))
        then return $ formula_type.const (e.const_name) "Bool"
        else if (ty = ```(int))
        then return $ formula_type.const (e.const_name) "Int"
        else if ty.is_arrow
        then formula_type_from_arrow (e.const_name) e
        else if prop_sorted
        then return formula_type.prop_formula
        else return formula_type.unsupported
   else if (ty = ```(Prop))
   then return formula_type.prop_formula
   else return formula_type.unsupported

meta def reflect_application (fn : expr) (args : list expr) (callback : expr → smt2_m term) : smt2_m term :=
    if fn.is_constant
    then term.apply (mangle_name fn.const_name) <$> monad.mapm callback args
    else if fn.is_local_constant
    then term.apply (mangle_name fn.local_uniq_name) <$> monad.mapm callback args
    else tactic.fail "the z3 tactic only supports local constants as uninterpreted head symbols"

/-- This function is the meat of the tactic, it takes a propositional formula in Lean, and transforms
   it into a corresponding term in SMT2.
-/
meta def reflect_arith_formula (reflect_base : expr → smt2_m term) : expr → smt2_m term
| ```(%%a + %%b) := smt2.builder.add <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(%%a - %%b) := smt2.builder.sub <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(%%a * %%b) := smt2.builder.mul <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(%%a / %%b) := smt2.builder.div <$> reflect_arith_formula a <*> reflect_arith_formula b
/- Constants -/
| ```(zero) := smt2.builder.int_const <$> eval_expr int ```(zero : int)
| ```(one) := smt2.builder.int_const <$> eval_expr int ```(one : int)
| ```(bit0 %%Bits) :=
  do ty ← infer_type Bits,
     if (ty = ```(int))
     then smt2.builder.int_const <$> eval_expr int ```(bit0 %%Bits : int)
     else if (ty = ```(nat))
     then smt2.builder.int_const <$> int.of_nat <$> eval_expr nat ```(bit0 %%Bits : nat)
     else tactic.fail $ "unknown numeric literal: " ++ (to_string ```(bit0 %%Bits : int))
| ```(bit1 %%Bits) :=
  do ty ← infer_type Bits,
     if (ty = ```(int))
     then smt2.builder.int_const <$> eval_expr int ```(bit1 %%Bits : int)
     else if (ty = ```(nat))
     then smt2.builder.int_const <$> (int.of_nat <$> eval_expr nat ```(bit1 %%Bits : nat))
     else tactic.fail $ "unknown numeric literal: " ++ (to_string ```(bit1 %%Bits : int))
| a :=
    if a.is_local_constant
    then return $ term.qual_id (mangle_name a.local_uniq_name)
    else if a.is_constant
    then return $ term.qual_id (mangle_name a.const_name)
    else if a.is_app
    then reflect_application (a.get_app_fn) (a.get_app_args) reflect_base
    else tactic.fail $ "unsupported arithmetic formula: " ++ to_string a

/-- Check if the type is an `int` or logically a subtype of an `int` like nat. -/
meta def is_int (e : expr) : tactic bool :=
do ty ← infer_type e,
   return $ (ty = ```(int)) || (ty = ```(nat))

meta def unsupported_ordering_on {α : Type} (elem : expr) : tactic α :=
do ty ← infer_type elem,
   tactic.fail $ "unable to translate orderings for values of type: " ++ to_string ty

-- I apologize for these crazy callbacks, we need a mutual keyword or section.
meta def reflect_ordering (reflect_arith : expr → smt2_m term) (R : term → term → term) (P Q : expr) : smt2_m term :=
do is ← is_int P, -- NB: P and Q should have the same type.
   if is
   then smt2.builder.lt <$> (reflect_arith P) <*> (reflect_arith Q)
   else unsupported_ordering_on P

meta def reflect_prop_formula' : expr → smt2_m term
| ```(¬ %%P) := not <$> (reflect_prop_formula' P)
| ```(%%P = %% Q) := smt2.builder.equals <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P ∧ %%Q) := smt2.builder.and2 <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P ∨ %%Q) := smt2.builder.or2 <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P ↔ %%Q) := smt2.builder.iff <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P < %%Q) := reflect_ordering (reflect_arith_formula reflect_prop_formula') smt2.builder.lt P Q
| ```(%%P <= %%Q) := reflect_ordering (reflect_arith_formula reflect_prop_formula') smt2.builder.lte P Q
| ```(%%P > %%Q) := reflect_ordering (reflect_arith_formula reflect_prop_formula') smt2.builder.gt P Q
| ```(%%P >= %%Q) := reflect_ordering (reflect_arith_formula reflect_prop_formula') smt2.builder.gte P Q
| e := if e.is_local_constant
       then return $ term.qual_id (mangle_name e.local_uniq_name)
       else if e = ```(int)
       then return "Int"
       else (do
         ty ← infer_type e,
         tactic.trace $ "expr: " ++ to_string e ++ ", inferred_type: " ++ to_string ty,
         if (ty = ```(int))
         then (do tactic.trace "arith", reflect_arith_formula reflect_prop_formula' e)
         else if e.is_arrow
         then (do tactic.trace "arrow" ,implies <$> (reflect_prop_formula' e.binding_domain) <*> (reflect_prop_formula' e.binding_body ))
         else if e.is_pi
         then do loc ← tactic.mk_local' e.binding_name e.binding_info e.binding_domain,
                 tactic.trace $ (expr.instantiate_var (e.binding_body) loc),
                 forallq (mangle_name $ loc.local_uniq_name) <$>
                      -- TODO: fix this
                      (type_to_sort $ e.binding_domain) <*>
                      (reflect_prop_formula' (expr.instantiate_var (e.binding_body) loc))
         else if e.is_app
         then do let fn := e.get_app_fn,
               let args := e.get_app_args,
            --    tactic.trace $ "app case: " ++ to_string e,
            --    tactic.trace $ "app case fn: " ++ to_string fn,
            --    tactic.trace $ "app case args: " ++ to_string args,
               -- we should probably relax for top-level constants which have already been translated
               if fn.is_local_constant
               then do args' ← monad.mapm reflect_prop_formula' args,
                       tactic.trace $ "arguments: " ++ args.to_string,
                       pure $ smt2.term.apply (mangle_name fn.local_uniq_name) args'
               else tactic.fail "can only handle fn constants right now"
          else tactic.fail $ "unsupported propositional formula : " ++ to_string e)

meta def reflect_prop_formula (e : expr) : smt2_m (builder unit) :=
do ty ← infer_type e,
   form ← reflect_prop_formula' ty,
   return $ assert form

meta def reflect_local (e : expr) : smt2_m (builder unit) :=
do ft ← classify_formula e,
   match ft with
   | formula_type.const n (sort.id "Bool") :=
     return $ declare_const (mangle_name n) "Bool"
   | formula_type.const n (sort.id "Int") :=
     return $ declare_const (mangle_name n) "Int"
   | formula_type.fn n ps rs :=
     return $ declare_fun (mangle_name n) ps rs
   | formula_type.prop_formula :=
     reflect_prop_formula e
   | _ := return (return ())
   end

meta def reflect_context : smt2_m (builder unit) :=
do ls ← local_context,
   bs ← monad.mapm reflect_local ls,
   return $ list.foldl (λ (a b : builder unit), a >> b) (return ()) bs

meta def reflect_attr_decl (n : name) : smt2_m (builder unit) :=
do tactic.trace (to_string n),
   exp ← mk_const n,
   reflect_local exp

/- Reflect the environment consisting of declarations with the `smt2` attribute. -/
meta def reflect_environment : smt2_m (builder unit) :=
do decls ← attribute.get_instances `smt2,
   bs ← monad.mapm reflect_attr_decl decls.reverse,
   return $ (monad.sequence bs >> return ())

meta def reflect_goal : smt2_m (builder unit) :=
do tgt ← target,
   ft ← classify_formula tgt,
   -- tactic.trace ("target: " ++ tgt.to_string),
   match ft with
   | formula_type.const n (sort.id "Bool") :=
      return $ assert (not $ mangle_name n)
   | formula_type.prop_formula :=
      do form ← reflect_prop_formula' tgt,
         return $ assert (not form)
   | _ := tactic.fail "unsupported goal"
   end

meta def reflect : smt2_m (builder unit) :=
do env_builder ← reflect_environment,
   ctxt_builder ← reflect_context,
   goal_builder ← reflect_goal,
   return $ env_builder >> ctxt_builder >> goal_builder >> check_sat

meta def z3 (log_file : option string := none) : tactic unit :=
do (builder, _) ← reflect smt2_state.initial,
   resp ← run_io (λ ioi, @smt2 ioi builder log_file),
   match resp with
   | response.sat := tactic.fail "z3 was unable to prove the goal"
   | response.unknown := tactic.fail "z3 was unable to prove the goal"
   | response.other str := tactic.fail $ "encountered unexpected response: `" ++ str ++ "`"
   | response.unsat := do
        tgt ← target,
        fresh_name ← mk_fresh_name,
        let axiom_name := name.mk_string "z3" (name.mk_string "axioms" fresh_name),
        -- TODO: generate a minimal unique axiom for each application of the tactic, add_decl (declaration.ax axiom_name [] tgt)
        sry ← to_expr $ `(sorry),
        exact sry
   end

