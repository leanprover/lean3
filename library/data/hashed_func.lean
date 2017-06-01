/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.hash_map

universes u v

namespace hashed_func
  variables {α : Type u} [decidable_eq α] {β : α → Type v}

  def cache_ty (f : Π a, β a) (hash_fn : α → ℕ) :=
  {m : hash_map α β // ∀ x y, m.find x = some y → f x = y}

  instance (f : Π a, β a) (hash_fn : α → ℕ) : inhabited (cache_ty f hash_fn) :=
  ⟨⟨mk_hash_map hash_fn, λx y h, by rw hash_map.find_empty at h; contradiction⟩⟩
end hashed_func

structure hashed_func (α : Type u) [decidable_eq α] (β : α → Type v) := mk' ::
(func : Π a, β a)
(hash_fn : α → ℕ)
(cache : cached (hashed_func.cache_ty func hash_fn))

namespace hashed_func
  variables {α : Type u} [decidable_eq α] {β : α → Type v}

  def mk (f : Π a, β a) (hash_fn : α → ℕ) : hashed_func α β := ⟨f, hash_fn, default _⟩

  def eval : hashed_func α β → Π a, β a | ⟨f, hash_fn, c⟩ a :=
  c.lift_on
    (λ⟨m, H⟩, (m.find a).get_or_else $
      let v := f a in c.update ⟨m.insert a v, λ x y h,
      begin
        by_cases a = x with ax,
        { revert y, rw -ax, intros y h,
          rw hash_map.find_insert_eq at h,
          injection h },
        { rw hash_map.find_insert_ne _ _ _ _ ax at h,
          exact H x y h }
      end⟩ v)
    (λ⟨m, H⟩, begin
      unfold default inhabited.default hashed_func.eval._match_1,
      rw hash_map.find_empty,
      ginduction m.find a with h b; dsimp [option.get_or_else, cached.update, hashed_func.eval._match_1],
      { refl },
      { exact H a b h },
    end)

  instance : has_coe_to_fun (hashed_func α β) := ⟨_, hashed_func.eval⟩

end hashed_func
