import system.io
import system.process
import .solvers.z3
import .syntax
import .builder

inductive smt2.response
| sat
| unsat
| other : string → smt2.response

meta def parse_smt2_result (str : string) : smt2.response :=
    if str = "sat\n"
    then smt2.response.sat
    else if str = "unsat\n"
    then smt2.response.unsat
    else smt2.response.other str

meta def smt2 [io.interface] (build : smt2.builder unit) : io smt2.response :=
do z3 ← z3_instance.start,
   io.put_str (to_string $ to_fmt build),
   res ← z3.raw (to_string $ to_fmt build),
   return $ parse_smt2_result res

open tactic
open smt2
open smt2.builder

meta def mangle_name (n : name) : string :=
    "lean_" ++ n^.to_string_with_sep "-"

meta def reflect_prop (e : expr) : tactic (builder unit) :=
return $ do let z3_name := mangle_name e.local_uniq_name,
   declare_const  z3_name "Bool"

meta def reflect_prop_formula' : expr → tactic term
| ```(¬ %%P) := not <$> (reflect_prop_formula' P)
| ```(%%P → %% Q) := implies <$> (reflect_prop_formula' P) <*> (reflect_prop_formula' Q)
| e := if e.is_local_constant
       then return $ term.qual_id (mangle_name e.local_uniq_name)
       else tactic.fail $ "unsupported propositional formula : " ++ to_string e

meta def reflect_prop_formula (e : expr) : tactic (builder unit) :=
do ty ← infer_type e,
   form ← reflect_prop_formula' ty,
   return $ assert form

inductive formula_type
| prop
| prop_formula
| unsupported

meta def classify_formula (e : expr) : tactic formula_type :=
do p ← is_prop e,
   if p
   then return formula_type.prop
   else
     do ty ← infer_type e,
        sort ← infer_type ty,
        -- add to our own tracing for this module? look at simplifier?
        tactic.trace ("type: " ++ to_string ty),
        tactic.trace ("sort: " ++ to_string sort),
        if sort = ```(Prop)
        then return formula_type.prop_formula
        else return formula_type.unsupported

meta def reflect_local (e : expr) : tactic (builder unit) :=
do ft ← classify_formula e,
   match ft with
   | formula_type.prop := reflect_prop e
   | formula_type.prop_formula := reflect_prop_formula e
   | _ := return (return ())
   end

meta def reflect_context : tactic (builder unit) :=
do ls ← local_context,
   bs ← monad.mapm reflect_local ls,
   return $ list.foldl (λ (a b : builder unit), a >> b) (return ()) bs

meta def reflect_goal : tactic (builder unit) :=
do tgt ← target,
   ft ← classify_formula tgt,
   match ft with
   | formula_type.prop :=
     do tgt ← target,
        let n := tgt.local_uniq_name,
        return $ assert (not $ mangle_name n)
   | _ :=
     return $ do declare_const "goal" "Bool",
        assert (not $ "goal")
--    | formula_type.prop_formula :=
--         do ty ← infer_type tgt,
--            form ← reflect_prop_formula' ty,
--            return $ assert (not form)
--    | _ := return (return ())
   end


axiom admit_ax : forall {A : Prop}, A

meta def z3 : tactic unit :=
do goal_builder ← reflect_goal,
   ctxt_builder ← reflect_context,
   resp ← run_io (λ ioi, @smt2 ioi (ctxt_builder >> goal_builder >> check_sat)),
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

