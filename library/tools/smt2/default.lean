-- declare_trace smt2
import system.io
import system.process
import .solvers.z3
import .syntax
import .builder
import .tactic

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

meta def reflect_prop (e : expr) : smt2_m (builder unit) :=
return $ do let z3_name := mangle_name e.local_uniq_name,
            declare_const  z3_name "Bool"

#check eval_expr

meta def as_literal : expr → option int := fun e, none


/-- This function is the meat of the tactic, it takes a propositional formula in Lean, and transforms
   it into a corresponding term in SMT2.
-/
meta def reflect_arith_formula : expr → smt2_m term
| ```(%%a + %%b) := smt2.builder.add <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(%%a - %%b) := smt2.builder.sub <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(%%a * %%b) := smt2.builder.mul <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(%%a / %%b) := smt2.builder.div <$> reflect_arith_formula a <*> reflect_arith_formula b
| ```(zero : int) := smt2.builder.int_const <$> eval_expr int ```(one : int)
| ```(one : int) := smt2.builder.int_const <$> eval_expr int ```(one : int)
| ```(bit0 %%Bits : int) := smt2.builder.int_const <$> eval_expr int ```(bit0 %%Bits : int)
| ```(bit1 %%Bits : int) := smt2.builder.int_const <$> eval_expr int ```(bit0 %%Bits : int)
| a :=
    if a.is_local_constant
    then return $ term.qual_id (mangle_name a.local_uniq_name)
    else tactic.fail $ "unsupported arithmetic formula: " ++ to_string a

meta def reflect_prop_formula' : expr → smt2_m term
| ```(¬ %%P) := not <$> (reflect_prop_formula' P)
| ```(%%P → %%Q) := implies <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P ∧ %%Q) := smt2.builder.and2 <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P ∨ %%Q) := smt2.builder.or2 <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P ↔ %%Q) := smt2.builder.iff <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| ```(%%P < %%Q) :=
do ty ← infer_type P,
if (ty = ```(int))
then smt2.builder.lt <$> (reflect_arith_formula P) <*> (reflect_arith_formula Q)
else tactic.fail "unknown ordering"
| e := do tactic.trace ("trace: " ++ to_string e ++ ", " ++ to_string e.local_uniq_name),
       if e.is_local_constant
       then return $ term.qual_id (mangle_name e.local_uniq_name)
       else tactic.fail $ "unsupported propositional formula : " ++ to_string e

meta def reflect_prop_formula (e : expr) : smt2_m (builder unit) :=
do ty ← infer_type e,
   form ← reflect_prop_formula' ty,
   return $ assert form

inductive formula_type
| const : smt2.sort → formula_type
| prop_formula
| unsupported

/-- The goal of this function is to categorize the set of formulas in the hypotheses,
   and goal, the assumptions this code is written under follow:

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
        then return $ formula_type.const "Bool"
        else if (ty = ```(int))
        then return $ formula_type.const "Int"
        else if prop_sorted
        then return formula_type.prop_formula
        else return formula_type.unsupported
   else if (ty = ```(Prop))
        then return formula_type.prop_formula
        else return formula_type.unsupported

meta def reflect_local (e : expr) : smt2_m (builder unit) :=
do ft ← classify_formula e,
   match ft with
   | formula_type.const (sort.id "Bool") := reflect_prop e
   | formula_type.const (sort.id "Int") :=
    return $ do let z3_name := mangle_name e.local_uniq_name,
            declare_const  z3_name "Int"
   | formula_type.prop_formula := reflect_prop_formula e
   | _ := return (return ())
   end

meta def reflect_context : smt2_m (builder unit) :=
do ls ← local_context,
   bs ← monad.mapm reflect_local ls,
   return $ list.foldl (λ (a b : builder unit), a >> b) (return ()) bs

meta def reflect_goal : smt2_m (builder unit) :=
do tgt ← target,
   ft ← classify_formula tgt,
   tactic.trace ("target: " ++ tgt.to_string),
   match ft with
   | formula_type.const (sort.id "Bool") :=
     do tactic.trace "variable case",
        let n := tgt.local_uniq_name,
        return $ assert (not $ mangle_name n)
   | formula_type.prop_formula :=
      do tactic.trace "prop case",
      (do form ← reflect_prop_formula' tgt, return $ assert (not form))
   | _ := tactic.fail "unknown goal"
   end

meta def reflect : smt2_m (builder unit) :=
do goal_builder ← reflect_goal,
   ctxt_builder ← reflect_context,
   return $ ctxt_builder >> goal_builder >> check_sat

meta def z3 : tactic unit :=
do (builder, _) ← reflect smt2_state.initial,
   resp ← run_io (λ ioi, @smt2 ioi builder),
   match resp with
   | response.sat := tactic.fail "z3 was unable to prove the goal"
   | response.other str := tactic.fail $ "encountered unexpected response: `" ++ str ++ "`"
   | response.unsat := do
        tgt ← target,
        fresh_name ← mk_fresh_name,
        let axiom_name := name.mk_string "z3" (name.mk_string "axioms" fresh_name),
        -- TODO: generate a minimal unique axiom for each application of the tactic, add_decl (declaration.ax axiom_name [] tgt)
        sry ← to_expr $ `(sorry),
        exact sry
   end

