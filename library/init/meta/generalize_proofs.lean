/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

prelude
import init.meta.tactic

namespace tactic

private meta def collect_proofs_in :
  expr → list name × list expr → tactic (list name × list expr) | e (ns, hs) :=
let go : tactic (list name × list expr) :=
(do t ← infer_type e,
    is_prop t >>= guardb,
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
        return (ns, h::hs))) <|> return (ns, hs) in
match e with
| (expr.const _ _)   := go
| (expr.local_const _ _ _ t) := collect_proofs_in t (ns, hs)
| (expr.mvar _ t)    := collect_proofs_in t (ns, hs)
| (expr.app f x)     :=
  go >>= collect_proofs_in f >>= collect_proofs_in x
| (expr.lam n b d e) :=
  go >>= collect_proofs_in d >>= collect_proofs_in e
| (expr.pi n b d e) :=
  collect_proofs_in d (ns, hs) >>= collect_proofs_in e
| (expr.elet n t d e) :=
  go >>= collect_proofs_in t >>= collect_proofs_in d >>= collect_proofs_in e
| (expr.macro m l) :=
  do x ← go, mfoldl (λ x e, collect_proofs_in e x) x l
| _                  := return (ns, hs)
end

meta def generalize_proofs (ns : list name) : tactic unit :=
do intros_dep,
   hs ← local_context >>= mfilter is_proof,
   t ← target,
   collect_proofs_in t (ns, hs) >> skip

end tactic