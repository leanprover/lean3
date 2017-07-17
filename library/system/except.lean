/-
Copyright (c) 2017 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
universes u v

inductive except (ε α : Type u)
| error {} : ε → except
| ok {} : α → except

def except.return {ε α : Type u} (a : α) : except ε α :=
except.ok a

def except.map {ε α β : Type u} (f : α → β) : except ε α → except ε β
| (except.error err) := except.error err
| (except.ok v) := except.ok $ f v

def except.bind {ε α β : Type u} (ma : except ε α) (f : α → except ε β) : except ε β :=
match ma with
| (except.error err) := except.error err
| (except.ok v) := f v
end

lemma except.id_map {ε α : Type u} (x : except ε α) : except.map id x = x :=
begin intros, cases x; dsimp [except.map]; reflexivity, end

lemma except.pure_bind {ε α β : Type u} (x : α) (f : α → except ε β) :
    except.bind (except.return x) f = f x :=
begin intros, dsimp [except.return, except.bind], reflexivity end

lemma except.bind_pure_comp_eq_map {ε  α β : Type u} (f : α → β) (x : except ε α) : (except.bind x) (except.return ∘ f) = except.map f x :=
begin
  intros,
  cases x; unfold except.bind except.map function.comp except.return,
end

instance except_monad (ε : Type u) : monad (except ε) :=
{ pure := @except.return ε,
  map := @except.map ε,
  bind := @except.bind ε,
  id_map := @except.id_map ε,
  pure_bind := @except.pure_bind ε,
  bind_pure_comp_eq_map := @except.bind_pure_comp_eq_map ε,
  bind_assoc := begin intros, cases x; dsimp [except.bind]; reflexivity end
}

@[reducible] def except_t (m : Type u → Type v) (ε α : Type u) :=
m (except ε α)

section except_t

parameter (m : Type u → Type v)
parameter [monad_m : monad m]
parameter ε : Type u

def except_t.return {α : Type u} (a : α) : except_t m ε α :=
@return m monad_m _ (except.ok a)

-- WHy doesn't this work anymore, this seems super annoying ...
-- Overall if we lost the ability for these types of projections working it seems like
-- a massive lose compared to the old style.
--
-- def except_t.map {α β : Type u} (f : α → β) (ma : except_t m ε α) : except_t m ε β :=
-- (@has_map.map m _ _ _) (except.map f) ma

-- This is super annoying ...
def except_t.map {α β : Type u} (f : α → β) (ma : except_t m ε α) : except_t m ε β :=
(@has_map.map m (monad_m.to_applicative.to_functor.to_has_map) _) _ (except.map f) ma

def except_t.bind {α β : Type u} (ma : except_t m ε α) (f : α → except_t m ε β) : except_t m ε β :=
(@has_bind.bind m monad_m.to_has_bind _ _) ma $
λ res, match res with
| (except.error err) := return $ except.error err
| (except.ok v) := f v
end

lemma except_t.id_map {α : Type u} (x : except_t m ε α) : except_t.map id x = x :=
begin
  intros,
  unfold except_t at x,
  dsimp [except_t.map],
  have P : @except.map ε α α id = id,
  apply funext,
  intros,
  rewrite except.id_map,
  simp,
  rewrite P,
  rw functor.id_map,
end

lemma except_t.pure_bind {α β : Type u} (x : α) (f : α → except_t m ε β) :
    except_t.bind (except_t.return x) f = f x :=
begin
  dsimp [except_t.return, except_t.bind],
  have pb := @monad.pure_bind,
  rewrite pb,
  reflexivity
end

lemma except_t.bind_assoc {α β γ : Type u} (x : except_t m ε α) (f : α → except_t m ε β) (g : β → except_t m ε γ):
  except_t.bind (except_t.bind x f) g = except_t.bind x (λ (x : α), except_t.bind (f x) g) :=
begin
  dsimp [except_t.bind],
  rewrite monad.bind_assoc,
  apply congr,
  simp,
  apply funext,
  intros,
  cases x_1,
  -- unfold has_bind.bind at *,
  admit,
  admit,
end

lemma except_t.bind_pure_comp_eq_map {α β : Type u} (f : α → β) (x : except_t m ε α) : (except_t.bind x) (except_t.return ∘ f) = except_t.map f x :=
begin
admit
  -- intros,
  -- unfold except_t at x,
  -- unfold except_t.bind except_t.map,
  -- rewrite -monad.bind_pure_comp_eq_map,
  -- apply congr ; simp,
  -- apply funext,
  -- intros,
  -- cases x_1,
  -- unfold except_t.bind._match_1,
  -- unfold function.comp,
  -- simp [except.map],
  -- unfold return pure,
  -- unfold function.comp,
  -- unfold except_t.bind._match_1,
  -- simp [except.map],
  -- unfold except_t.return,
  -- reflexivity,
end

def except_t.run {α : Type u} (res : except_t m ε α) : m (except ε α) := res

end except_t

instance except_t_is_monad (m : Type u → Type v) [monad m] (ε : Type u) : monad (except_t m ε) :=
{ pure := @except_t.return m _ ε ,
  map := @except_t.map m _ ε,
  bind := @except_t.bind m _ ε,
  id_map := @except_t.id_map m _ ε,
  pure_bind := @except_t.pure_bind m _ ε,
  bind_assoc := @except_t.bind_assoc m _ ε,
  bind_pure_comp_eq_map := @except_t.bind_pure_comp_eq_map m _ ε
}
