/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
prelude
import init.data.quot
universes u v

structure cached (α : Type u) [inhabited α] := mk' :: (val : quot (λ x y : α, true))

namespace cached

variables {α : Type u} [inhabited α] {β : Type v}

def mk (v : α) : cached α := ⟨quot.mk _ v⟩

def empty : cached α := mk (default α)

def lift (f : α → β) (h : ∀ x y, f x = f y) (c : cached α) : β :=
quot.lift f (λx y _, h x y) c.val

def lift_eq {f : α → β} {h} (x) : lift f h (mk x) = f x := rfl

-- This function has a VM implementation to change the value of the cache `c` to `v`
def update (c : cached α) (v : α) (f : thunk β) : β := f ()

def reset (c : cached α) : thunk β → β := update c (default α)

theorem cache_eq_empty : ∀ (c : cached α), c = empty
| ⟨q⟩ := congr_arg mk' $ quot.ind (λx, quot.sound trivial) q

end cached