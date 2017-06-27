/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

prelude
import init.meta.tactic

namespace tactic

private meta def collect_proofs_in :
  expr → list expr → list name × list expr → tactic (list name × list expr)
| e ctx (ns, hs) :=
let go (tac : list name × list expr → tactic (list name × list expr)) :
  tactic (list name × list expr) :=
do t ← infer_type e,
   mcond (is_prop t) (do
     first (hs.map $ λ h, do
       t' ← infer_type h,
       is_def_eq t t',
       g ← target,
       change $ g.replace (λ a n, if a = e then some h else none),
       return (ns, hs)) <|>
     (let (n, ns) := (match ns with
        | [] := (`_x, [])
        | (n :: ns) := (n, ns)
        end : name × list name) in
      do generalize e n,
         h ← intro n,
         return (ns, h::hs)) <|> return (ns, hs)) (tac (ns, hs)) in
match e with
| (expr.const _ _)   := go return
| (expr.local_const _ _ _ t) := collect_proofs_in t ctx (ns, hs)
| (expr.mvar _ t)    := collect_proofs_in t ctx (ns, hs)
| (expr.app f x)     :=
  go (λ nh, collect_proofs_in f ctx nh >>= collect_proofs_in x ctx)
| (expr.lam n b d e) :=
  go (λ nh, do
    nh ← collect_proofs_in d ctx nh,
    var ← mk_local' n b d,
    collect_proofs_in (expr.instantiate_var e var) (var::ctx) nh)
| (expr.pi n b d e) := do
  nh ← collect_proofs_in d ctx (ns, hs),
  var ← mk_local' n b d,
  collect_proofs_in (expr.instantiate_var e var) (var::ctx) nh
| (expr.elet n t d e) :=
  go (λ nh, do
    nh ← collect_proofs_in t ctx nh,
    nh ← collect_proofs_in d ctx nh,
    collect_proofs_in (expr.instantiate_var e d) ctx nh)
| (expr.macro m l) :=
  go (λ nh, mfoldl (λ x e, collect_proofs_in e ctx x) nh l)
| _                  := return (ns, hs)
end

meta def generalize_proofs (ns : list name) : tactic unit :=
do intros_dep,
   hs ← local_context >>= mfilter is_proof,
   t ← target,
   collect_proofs_in t [] (ns, hs) >> skip

end tactic
