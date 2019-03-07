prelude
import init.meta.tactic
open tactic expr

-- meta constant add_ginductive : list name → list expr → list expr → list (list expr) → bool → tactic unit
#check add_ginductive
  run_cmd
do -- t ← mk_local_def `foo `(Type),
   let c := @const tt `foo [],
   v ← mk_local_def `foo `(Type),
   c ← mk_local_def `constr (const `foo []),
   add_ginductive [] [] [v] [[c]] ff
   -- `foo [] 0 `(Type) [(`constr,c)]

mutual inductive odd, even (α : Type)
with odd : ℕ → Prop
| zero : odd 0
with even : ℕ → Prop
| one : even 1



#check foo.no_confusion
