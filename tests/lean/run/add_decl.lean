prelude
import init.meta.tactic
open tactic expr

/-
inductive foo (α : Type)
| constr : foo
-/

run_cmd do
  α ← mk_local_def `α `(Type),
  let c : expr := (@const tt `foo []).app α,
  env ← get_env,
  env.add_ginductive options.mk
    [] [α] [((`foo, `(Type)), [⟨`foo.constr, c, default _⟩])] ff >>= set_env

#print foo

/-
mutual inductive odd, even (α : Type) (zero : α) (succ : α → α)
with odd : α → Prop
| succ {n} : even n → odd (succ n)
with even : α → Prop
| zero : even zero
| succ {n} : odd n → even (succ n)
-/

run_cmd do
  env ← get_env,
  α ← mk_local_def `α `(Type),
  zero ← mk_local_def `zero α,
  succ ← mk_local_def `succ `((%%α : Type) → (%%α : Type)),
  let odd : expr := (@const tt `odd []).app α zero succ,
  let even : expr := (@const tt `even []).app α zero succ,
  let pred := `((%%α : Type) → Prop),
  n ← mk_local' `n binder_info.implicit α,
  let odd_succ_ty := `((%%(even n) : Prop) → (%%(odd (succ n)) : Prop)).bind_pi n,
  let even_succ_ty := `((%%(odd n) : Prop) → (%%(even (succ n)) : Prop)).bind_pi n,
  pp odd_succ_ty >>= trace,
  env.add_ginductive options.mk
    [] [α, zero, succ] [
      ((`odd, `((%%α : Type) → Prop)),
        [⟨`odd.succ, odd_succ_ty, default _⟩]),
      ((`even, `((%%α : Type) → Prop)),
        [⟨`even.zero, even zero, default _⟩,
         ⟨`even.succ, even_succ_ty, default _⟩])] ff >>= set_env

#print prefix odd
#print prefix even
