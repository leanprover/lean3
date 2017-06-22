/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
prelude
import init.data.quot init.data.option.basic init.util
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

  -- This function has a VM implementation to change the value of the cache `c` to `v`
  def update (c : cached α) (v : α) (f : thunk β) : β := f ()

  @[simp] lemma update_def (c : cached α) (v : α) (f : thunk β) :
    @update _ _ _ c v f = f () := rfl

  def reset (c : cached α) : thunk β → β := update c (default α)

  @[simp] lemma reset_def (c : cached α) (f : thunk β) :
    @reset _ _ _ c f = f () := rfl

  theorem cache_eq_empty : ∀ (c : cached α), c = empty
  | ⟨q⟩ := congr_arg mk' $ quot.ind (λx, quot.sound trivial) q

  @[simp] lemma lift_mk {f : α → β} {h} (x) : lift_on (mk x) f h = f x := rfl

  meta def inspect (c : cached α) : α := unchecked_cast c.val

  meta instance [has_to_string α] : has_to_string (cached α) := ⟨to_string ∘ inspect⟩

  meta instance [has_repr α] : has_repr (cached α) := ⟨repr ∘ inspect⟩

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

  @[simp] theorem mk_eval (f : unit → α) : (@mk _ f).eval = f () := rfl

  @[simp] theorem eval_val : ∀ (f : memoized α), eval f = f.func ()
  | ⟨f, c⟩ := congr_arg (λ c', eval ⟨f, c'⟩) c.cache_eq_empty

  instance : has_coe_to_fun (memoized α) := ⟨λ_, thunk α, λm _, m.eval⟩

  instance : has_coe (memoized α) α := ⟨λm, m.eval⟩

end memoized
