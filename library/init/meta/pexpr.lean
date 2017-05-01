/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude

import init.meta.expr

universe u

-- meta inductive equations (f : () -> Type) : Type
-- | empty {} : equations
-- | equation : (f ())  → equations

/- Quoted expressions. They can be converted into expressions by using a tactic. -/
meta inductive pexpr : Type
| var         : nat → pexpr
| sort        : level → pexpr
| const       : name → list level → pexpr
| mvar        : name → pexpr → pexpr
| local_const : name → name → binder_info → pexpr → pexpr
| app         : pexpr → pexpr → pexpr
| lam         : name → binder_info → pexpr → pexpr → pexpr
| pi          : name → binder_info → pexpr → pexpr → pexpr
| elet        : name → pexpr → pexpr → pexpr → pexpr
| macro       : macro_def → ∀ n, (fin n → pexpr) → pexpr
-- | prenum      : int → pexpr
| prenum      : nat → pexpr
| equations   : list (pexpr × pexpr) → pexpr

protected meta constant pexpr.of_expr  : expr → pexpr
protected meta constant pexpr.subst    : pexpr → pexpr → pexpr

/- Low level primitives for accessing internal representation. -/
protected meta constant pexpr.to_raw_expr : pexpr → expr
protected meta constant pexpr.of_raw_expr : expr → pexpr
meta constant pexpr.mk_placeholder : pexpr

meta constant pexpr.pos : pexpr → option pos

meta constant pexpr.mk_quote_macro : pexpr → pexpr
meta constant pexpr.mk_prenum_macro : nat → pexpr
meta constant pexpr.mk_string_macro : string → pexpr
meta constant pexpr.mk_field_macro : pexpr → name → pexpr
meta constant pexpr.mk_explicit : pexpr → pexpr

meta constant pexpr.to_string : pexpr → string
meta instance : has_to_string pexpr :=
⟨pexpr.to_string⟩

meta class has_to_pexpr (α : Type u) :=
(to_pexpr : α → pexpr)

meta def to_pexpr {α : Type u} [has_to_pexpr α] : α → pexpr :=
has_to_pexpr.to_pexpr

meta instance : has_to_pexpr pexpr :=
⟨id⟩

meta instance : has_to_pexpr expr :=
⟨pexpr.of_expr⟩
