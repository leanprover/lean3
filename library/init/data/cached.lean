/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
prelude
import init.data.quot init.data.option.basic
universes u v

structure cached (α : Type u) [inhabited α] :=
mk' :: (val : quot (λ x y : α, true))

namespace cached
  variables {α : Type u} [inhabited α] {β : Type v}

  def mk (v : α) : cached α := ⟨quot.mk _ v⟩

  def empty : cached α := mk (default α)
  instance : inhabited (cached α) := ⟨empty⟩

  def lift_on (c : cached α) (f : α → β) (h : ∀ x, f (default _) = f x) : β :=
  quot.lift f (λx y _, (h x).symm.trans (h y)) c.val

  def lift_eq {f : α → β} {h} (x) : lift_on (mk x) f h = f x := rfl

  -- This function has a VM implementation to change the value of the cache `c` to `v`
  def update (c : cached α) (v : α) (f : thunk β) : β := f ()

  def reset (c : cached α) : thunk β → β := update c (default α)

  theorem cache_eq_empty : ∀ (c : cached α), c = empty
  | ⟨q⟩ := congr_arg mk' $ quot.ind (λx, quot.sound trivial) q

end cached

structure memoized (α : Type u) := mk' ::
(func : unit → α)
(cache : cached (option {a // func () = a}))

namespace memoized
  variable {α : Type u}

  def mk (f : thunk α) : memoized α := mk' f (default _)

  def eval : memoized α → α | ⟨f, c⟩ :=
  c.lift_on
    (λo, match o with
      | none := let v := f () in c.update (some ⟨v, rfl⟩) v
      | some ⟨x, h⟩ := x
      end)
    (λo, match o with
      | none        := rfl
      | some ⟨x, h⟩ := h
      end)

  instance : has_coe_to_fun (memoized α) := ⟨λ_, thunk α, λm _, m.eval⟩

  instance : has_coe (memoized α) α := ⟨λm, m.eval⟩

end memoized
