/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
open nat tactic environment expr list

private meta def at_end₂ (e₁ e₂ : expr) : ℕ → tactic (list (option expr))
| 2 := return [some e₁, some e₂]
| (n+3) :=  (λ xs, none :: xs) <$> at_end₂ (n+2)
| _ := fail "at_end expected arity > 1"

-- Auxiliary function for introducing the new equalities produced by the
-- injection tactic
private meta def injection_intro : expr → list name → tactic (list expr × list name)
| (pi n bi b d) ns := do
  let hname := @head _ ⟨`h⟩ ns,
  h ← intro hname,
  (l, ns') ← injection_intro d (tail ns),
  return (h :: l, ns')
| e  ns           := return ([], ns)

-- Tries to decompose the given expression by constructor injectivity.
-- Returns the list of new hypotheses, and the remaining names from the given list,
-- or none if the goal was closed.
meta def injection_with (h : expr) (ns : list name) : tactic (option (list expr × list name)) :=
do
  ht ← infer_type h,
  (lhs0, rhs0) ← match_eq ht,
  env ← get_env,
  lhs ← whnf lhs0,
  rhs ← whnf rhs0,
  let n_fl := const_name (get_app_fn lhs),
  let n_fr := const_name (get_app_fn rhs),
  if n_fl = n_fr then do
    let n_inj := n_fl <.> "inj_arrow",
    if env.contains n_inj then do
      c_inj  ← mk_const n_inj,
      arity  ← get_arity c_inj,
      tgt ← target,
      args   ← at_end₂ h tgt (arity - 1),
      pr     ← mk_mapp n_inj args,
      pr_type ← infer_type pr,
      pr_type ← whnf pr_type,
      eapply pr,
      try (clear h),
      some <$> injection_intro (binding_domain pr_type) ns
    else fail "injection tactic failed, argument must be an equality proof where lhs and rhs are of the form (c ...), where c is a constructor"
  else
  let Il := name.get_prefix n_fl,
      Ir := name.get_prefix n_fr in
  if Il = Ir then do
    tgt ← target,
    pr ← mk_app (Il <.> "no_confusion") [tgt, lhs, rhs, h],
    exact pr,
    return none
  else if lhs.is_local_constant || rhs.is_local_constant then
    subst h >> return (some ([], ns))
  else
    fail "injection tactic failed, argument must be an equality proof where lhs and rhs are of the form (c ...), where c is a constructor"

meta def injection (h : expr) : tactic (list expr) :=
do o ← injection_with h [],
   return $ option.rec [] prod.fst o

meta def injections_with : nat → list expr → list name → tactic unit
| 0     lc        ns := fail "recursion depth exceeded"
| (n+1) []        ns := skip
| (n+1) (h :: lc) ns :=
  do o ← try_core (injection_with h ns), match o with
  | none                  := injections_with (n+1) lc ns
  | some none             := skip
  | some (some ([], ns')) := injections_with (n+1) lc ns'
  | some (some (t, ns'))  := injections_with n (t ++ lc) ns'
  end

end tactic
