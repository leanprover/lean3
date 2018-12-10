/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.format init.function

inductive congr_arg_kind
/- It is a parameter for the congruence lemma, the parameter occurs in the left and right hand sides. For example the α in the congruence generated from `f:Π {α}, α → α` -/
| fixed
/- It is not a parameter for the congruence lemma, the lemma was specialized for this parameter.
   This only happens if the parameter is a subsingleton/proposition, and other parameters depend on it. -/
| fixed_no_param
/- The lemma contains three parameters for this kind of argument a_i, b_i and (eq_i : a_i = b_i).
   a_i and b_i represent the left and right hand sides, and eq_i is a proof for their equality. -/
| eq
/- congr-simp lemma contains only one parameter for this kind of argument, and congr-lemmas contains two.
   They correspond to arguments that are subsingletons/propositions. For example the `p` in the congruence generated from `f:Π (P:Prop) (p:P), P`  -/
| cast
/- The lemma contains three parameters for this kind of argument a_i, b_i and (eq_i : a_i == b_i).
   a_i and b_i represent the left and right hand sides, and eq_i is a proof for their heterogeneous equality. -/
| heq

/-- 
A congruence lemma is a proof that two terms are equal (or some other relation) using a congruence proof.
An example of a congruence lemma is `∀ a₁ a₂, (a₁ ↔ a₂) → ∀ b₁ b₂, (b₁ ↔ b₂) → a₁ ∧ b₁ ↔ a₂ ∧ b₂`.
The conclusion is prepended by a set of arguments. `arg_kinds` gives a suggestion of how that argument should be filled in using a simplifier.
[NOTE] The number of arguments that `proof` takes can be inferred from `arg_kinds`: `arg_kinds.sum (fixed,cast ↦ 1|eq,heq ↦ 3 | fixed_no_param ↦ 0)`.
  -/
meta structure congr_lemma :=
(type : expr)
(proof : expr)
(arg_kinds : list congr_arg_kind)

namespace tactic
/--
`mk_congr_lemma_simp f nargs md`
creates a congruence lemma for the simplifier for the given function argument `f`.
If `nargs` is not none, then it tries to create a lemma for an application of arity `nargs`.
If `nargs` is none then the number of arguments will be guessed from the type signature of `f`.
That is, given `f : α → β → γ → δ` and `nargs = some 2`, we get a congruence lemma:
``` lean
{ type := ∀ a₁ a₂ : α, a₁ = a₂ → ∀ b₁ b₂ : β, b₁ = b₂ → f a₁ b₁ = f a₂ b₂
, proof := ...
, arg_kinds := [eq,eq]
}
```
See the docstrings for the cases of `congr_arg_kind` for more detail on how `arg_kinds` are chosen.
It can be difficult to see how the system chooses the `arg_kinds`, but it depends on what the other arguments depend on and whether the arguments have subsingleton types.
-/
meta constant mk_congr_lemma_simp (f : expr) (nargs : option nat := none) (md := semireducible) : tactic congr_lemma
/-- Create a specialized theorem using (a prefix of) the arguments of the given application. [TODO] I can't get this to produce anything except `h = h`. -/
meta constant mk_specialized_congr_lemma_simp (h : expr) (md : transparency := semireducible) : tactic congr_lemma

/-- [TODO] what is the difference between this and `mk_congr_lemma_simp`? -/
meta constant mk_congr_lemma (h : expr) (nargs : option nat := none) (md := semireducible) : tactic congr_lemma
/-- Create a specialized theorem using (a prefix of) the arguments of the given application. -/
meta constant mk_specialized_congr_lemma (h : expr) (md := semireducible) : tactic congr_lemma

/-- Make a congruence lemma using higher equality `heq` instead of `eq`.
For example `mk_hcongr_lemma (f : Π (α : ℕ → Type) (n:ℕ) (b:α n), ℕ` )` will make

``` lean
{ type := ∀ α α', α = α' → ∀ n n', n = n' → ∀ (b : α n) (b' : α' n'), b == b' → f α n b == f α' n' b'
, proof := ...
, arg_kinds := [eq,eq,heq]
}
```

(Using merely `mk_congr_lemma` instead will produce `[fixed,fixed,eq]` instaed.)
-/
meta constant mk_hcongr_lemma (h : expr) (nargs : option nat := none) (md := semireducible) : tactic congr_lemma

end tactic
