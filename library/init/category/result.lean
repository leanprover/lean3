prelude

import init.logic init.category.monad init.category.alternative

universe u

inductive result (E A : Type u)
| error {} : E → result
| ok {} : A → result

def result.return {E A : Type u} (a : A) : result E A :=
  result.ok a

def result.map {E A B : Type u} (f : A → B) : result E A → result E B
| (result.error err) := result.error err
| (result.ok v) := result.ok $ f v

def result.bind {E A B : Type u} (ma : result E A) (f : A → result E B) : result E B :=
   match ma with
   | (result.error err) := result.error err
   | (result.ok v) := f v
   end

instance (E : Type u) : monad (result E) :=
  { pure := @result.return E ,
    map := @result.map E,
    bind := @result.bind E }

@[reducible] def except_t (M : Type u → Type u) (E A : Type u) :=
  M (result E A)

section except_t

parameter (M : Type u → Type u)
parameter [monad_M : monad M]
parameter E : Type u

def except_t.return {A : Type u} (a : A) : except_t M E A :=
  (@monad.pure M monad_M _) (result.ok a)

def except_t.map {A B : Type u} (f : A → B) (ma : except_t M E A) : except_t M E B :=
  (@monad.map M monad_M _ _) (fun res, result.map f res) ma

def except_t.bind {A B : Type u} (ma : except_t M E A) (f : A → except_t M E B) : except_t M E B :=
   (@monad.bind M monad_M _ _) ma $
   fun res, match res with
   | (result.error err) := return $ result.error err
   | (result.ok v) := f v
   end

end except_t

instance (M : Type u → Type u) [monad M] (E : Type u) : monad (except_t M E) :=
  { pure := @except_t.return M _ E ,
    map := @except_t.map M _ E,
    bind := @except_t.bind M _ E }
