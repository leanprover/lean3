/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.declaration init.meta.exceptional init.data.option.basic
import init.meta.rb_map

/-- An __environment__ contains all of the declarations and notation that have been defined so far.   -/
meta constant environment : Type

namespace environment
/--
Consider a type ψ which is an inductive datatype using a single constructor `mk (a : α) (b : β) : → ψ`.
Lean will automatically make two projection functions `a : ψ → α`, `b : ψ → β`.
Lean tags these declarations as __projections__.
This helps the simplifier / rewriter not have to expand projectors.
Eg `a (mk x y)` will automatically reduce to `x`.
If you `extend` a structure, all of the projections on the parent will also be created for the child.

[TODO] any other reasons Lean treats projections differently to regular declarations?
    I know that you get projection macros.
[TODO] Are there projections that aren't arguments to constructors?
[NOTE] projectors have nothing to do with the dot `mylist.map` syntax.

You can find out if a declaration is a projection using `environment.is_projection` which returns `projection_info`.

Data for a projection declaration:
- `cname`    is the name of the constructor associated with the projection.
- `nparams`  is the number of constructor parameters. Eg `and.intro` has two type parameters.
- `idx`      is the parameter being projected by this projection.
- `is_class` is tt iff this is a typeclass projection.

### Examples:

- `and.right` is a projection with ``{cname := `and.intro, nparams := 2, idx := 1, is_class := ff}``
- `ordered_ring.neg` is a projection with ``{cname := `ordered_ring.mk, nparams := 1, idx := 5, is_class := tt}``.

-/
structure projection_info :=
(cname : name)
(nparams : nat)
(idx : nat)
(is_class : bool)

/-- A marking on the binders of structures and inductives indicating
   how this constructor should mark its parameters.

       inductive foo
       | one {} : foo -> foo   -- relaxed_implicit
       | two ( ) : foo -> foo   -- none
       | three : foo -> foo    -- implicit (default)
-/
inductive implicit_infer_kind | implicit | relaxed_implicit | none
instance implicit_infer_kind.inhabited : inhabited implicit_infer_kind := ⟨implicit_infer_kind.implicit⟩

/-- One introduction rule in an inductive declaration -/
meta structure intro_rule :=
(constr : name)
(type : expr)
(infer : implicit_infer_kind := implicit_infer_kind.implicit)

/-- Create a standard environment using the given trust level -/
meta constant mk_std          : nat → environment
/-- Return the trust level of the given environment -/
meta constant trust_lvl       : environment → nat
/-- Add a new declaration to the environment -/
meta constant add             : environment → declaration → exceptional environment
/-- Retrieve a declaration from the environment -/
meta constant get             : environment → name → exceptional declaration
meta def      contains (env : environment) (d : name) : bool :=
match env.get d with
| exceptional.success _      := tt
| exceptional.exception ._ _ := ff
end

meta constant add_defn_eqns (env : environment) (opt : options)
  (lp_params : list name) (params : list expr) (sig : expr)
  (eqns : list (list (expr ff) × expr)) (is_meta : bool) : exceptional environment

/-- Register the given name as a namespace, making it available to the `open` command -/
meta constant add_namespace   : environment → name → environment
/-- Return tt iff the given name is a namespace -/
meta constant is_namespace    : environment → name → bool
/-- Add a new inductive datatype to the environment
   name, universe parameters, number of parameters, type, constructors (name and type), is_meta -/
meta constant add_inductive (env : environment)
  (n : name) (levels : list name) (num_params : nat) (type : expr)
  (intros : list (name × expr)) (is_meta : bool) : exceptional environment
/-- Add a new general inductive declaration to the environment.
  This has the same effect as a `inductive` in the file, including generating
  all the auxiliary definitions, as well as triggering mutual/nested inductive
  compilation, by contrast to `environment.add_inductive` which only adds the
  core axioms supported by the kernel.

  The `inds` argument should be a list of inductives in the mutual family.
  The first argument is a pair of the name of the type being constructed
  and the type of this inductive family (not including the params).
  The second argument is a list of intro rules, specified by a name, an
  `implicit_infer_kind` giving the implicitness of the params for this constructor,
  and an expression with the type of the constructor (not including the params).
-/
meta constant add_ginductive (env : environment) (opt : options)
  (levels : list name) (params : list expr)
  (inds : list ((name × expr) × list intro_rule))
  (is_meta : bool) : exceptional environment
/-- Return tt iff the given name is an inductive datatype -/
meta constant is_inductive    : environment → name → bool
/-- Return tt iff the given name is a constructor -/
meta constant is_constructor  : environment → name → bool
/-- Return tt iff the given name is a recursor -/
meta constant is_recursor     : environment → name → bool
/-- Return tt iff the given name is a recursive inductive datatype -/
meta constant is_recursive    : environment → name → bool
/-- Return the name of the inductive datatype of the given constructor. -/
meta constant inductive_type_of : environment → name → option name
/-- Return the constructors of the inductive datatype with the given name -/
meta constant constructors_of : environment → name → list name
/-- Return the recursor of the given inductive datatype -/
meta constant recursor_of     : environment → name → option name
/-- Return the number of parameters of the inductive datatype -/
meta constant inductive_num_params : environment → name → nat
/-- Return the number of indices of the inductive datatype -/
meta constant inductive_num_indices : environment → name → nat
/-- Return tt iff the inductive datatype recursor supports dependent elimination -/
meta constant inductive_dep_elim : environment → name → bool
/-- Functionally equivalent to `is_inductive`.

Technically, this works by checking if the name is in the ginductive environment
extension which is outside the kernel, whereas `is_inductive` works by looking at the kernel extension.
But there are no `is_inductive`s which are not `is_ginductive`.
 -/
meta constant is_ginductive : environment → name → bool
/-- See the docstring for `projection_info`. -/
meta constant is_projection : environment → name → option projection_info
/-- Fold over declarations in the environment. -/
meta constant fold {α :Type} : environment → α → (declaration → α → α) → α
/-- `relation_info env n` returns some value if n is marked as a relation in the given environment.
   the tuple contains: total number of arguments of the relation, lhs position and rhs position. -/
meta constant relation_info : environment → name → option (nat × nat × nat)
/-- `refl_for env R` returns the name of the reflexivity theorem for the relation R -/
meta constant refl_for : environment → name → option name
/-- `symm_for env R` returns the name of the symmetry theorem for the relation R -/
meta constant symm_for : environment → name → option name
/-- `trans_for env R` returns the name of the transitivity theorem for the relation R -/
meta constant trans_for : environment → name → option name
/-- `decl_olean env d` returns the name of the .olean file where d was defined.
   The result is none if d was not defined in an imported file. -/
meta constant decl_olean : environment → name → option string
/-- `decl_pos env d` returns the source location of d if available. -/
meta constant decl_pos : environment → name → option pos
/-- Return the fields of the structure with the given name, or `none` if it is not a structure -/
meta constant structure_fields : environment → name → option (list name)
/-- `get_class_attribute_symbols env attr_name` return symbols
   occurring in instances of type classes tagged with the attribute `attr_name`.
   Example: [algebra] -/
meta constant get_class_attribute_symbols : environment → name → name_set
/-- The fingerprint of the environment is a hash formed from all of the declarations in the environment. -/
meta constant fingerprint : environment → nat

meta constant load_foreign_object (env : environment) (n : name) (file_name : string) : environment


open expr

meta constant unfold_untrusted_macros : environment → expr → expr
meta constant unfold_all_macros : environment → expr → expr

meta def is_constructor_app (env : environment) (e : expr) : bool :=
is_constant (get_app_fn e) && is_constructor env (const_name (get_app_fn e))

meta def is_refl_app (env : environment) (e : expr) : option (name × expr × expr) :=
match (refl_for env (const_name (get_app_fn e))) with
| (some n) :=
    if get_app_num_args e ≥ 2
    then some (n, app_arg (app_fn e), app_arg e)
    else none
| none   := none
end

/-- Return true if 'n' has been declared in the current file -/
meta def in_current_file (env : environment) (n : name) : bool :=
(env.decl_olean n).is_none && env.contains n

meta def is_definition (env : environment) (n : name) : bool :=
match env.get n with
| exceptional.success (declaration.defn _ _ _ _ _ _) := tt
| _                                                  := ff
end

end environment

meta instance : has_repr environment :=
⟨λ e, "[environment]"⟩

meta instance : inhabited environment :=
⟨environment.mk_std 0⟩
