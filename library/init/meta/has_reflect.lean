/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.expr init.util

universes u v

/-- `has_reflect α` lets you produce an `expr` from an instance of α. That is, it is a function from α to expr such that the expr has type α. -/
@[reducible] meta def has_reflect (α : Sort u) := Π a : α, reflected a

meta structure reflected_value (α : Type u) :=
(val : α)
[reflect : reflected val]

namespace reflected_value

meta def expr {α : Type u} (v : reflected_value α) : expr := v.reflect

meta def subst {α : Type u} {β : Type v} (f : α → β) [rf : reflected f]
  (a : reflected_value α) : reflected_value β :=
@mk _ (f a.val) (rf.subst a.reflect)

end reflected_value

section
local attribute [semireducible] reflected

meta instance nat.reflect : has_reflect ℕ
| n := if n = 0 then `(0 : ℕ)
       else if n = 1 then `(1 : ℕ)
       else if n % 2 = 0 then `(bit0 %%(nat.reflect (n / 2)) : ℕ)
       else `(bit1 %%(nat.reflect (n / 2)) : ℕ)

meta instance unsigned.reflect : has_reflect unsigned
| ⟨n, pr⟩ := `(unsigned.of_nat' n)

end

/- Instances that [derive] depends on. All other basic instances are defined at the end of
   derive.lean. -/

meta instance name.reflect : has_reflect name
| name.anonymous        := `(name.anonymous)
| (name.mk_string  s n) := `(λ n, name.mk_string  s n).subst (name.reflect n)
| (name.mk_numeral i n) := `(λ n, name.mk_numeral i n).subst (name.reflect n)

meta instance list.reflect {α : Type} [has_reflect α] [reflected α] : has_reflect (list α)
| []     := `([])
| (h::t) := `(λ t, h :: t).subst (list.reflect t)

meta instance punit.reflect : has_reflect punit
| () := `(_)
