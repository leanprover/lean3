prelude

import init.logic init.category.monad init.category.alternative

universes u v

inductive result (ε α : Type u)
| error {} : ε → result
| ok {} : α → result

def result.return {ε α : Type u} (a : α) : result ε α :=
result.ok a

def result.map {ε α β : Type u} (f : α → β) : result ε α → result ε β
| (result.error err) := result.error err
| (result.ok v) := result.ok $ f v

def result.bind {ε α β : Type u} (ma : result ε α) (f : α → result ε β) : result ε β :=
match ma with
| (result.error err) := result.error err
| (result.ok v) := f v
end

instance (ε : Type u) : monad (result ε) :=
{ pure := @result.return ε ,
  map := @result.map ε,
  bind := @result.bind ε }

@[reducible] def except_t (m : Type u → Type v) (ε α : Type u) :=
m (result ε α)

section except_t

parameter (m : Type u → Type v)
parameter [monad_m : monad m]
parameter ε : Type u

def except_t.return {α : Type u} (a : α) : except_t m ε α :=
(@monad.pure m monad_m _) (result.ok a)

def except_t.map {α β : Type u} (f : α → β) (ma : except_t m ε α) : except_t m ε β :=
(@monad.map m monad_m _ _) (result.map f) ma

def except_t.bind {α β : Type u} (ma : except_t m ε α) (f : α → except_t m ε β) : except_t m ε β :=
(@monad.bind m monad_m _ _) ma $
λ res, match res with
| (result.error err) := return $ result.error err
| (result.ok v) := f v
end

end except_t

instance (m : Type u → Type v) [monad m] (ε : Type u) : monad (except_t m ε) :=
{ pure := @except_t.return m _ ε ,
  map := @except_t.map m _ ε,
  bind := @except_t.bind m _ ε }
