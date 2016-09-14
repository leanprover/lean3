namespace system

set_option new_elaborator true

-- I'm extending the stdlib tho, which is good, we now have a system.result 
inductive result : Type -> Type -> Type
| err : Π {E R}, E -> result E R
| ok : Π {E R}, R -> result E R

-- TODO: elaborator is still underway, eventually clean these up, hacking around elab bugs
definition unwrap_or : Π {E T : Type}, result E T -> T -> T
| E T (result.err _) default := default
| _ T (result.ok t) _ := t

definition result.map : Π {E T U : Type}, (T → U) → result E T → result E U
| E T U f (result.err e) := result.err e
| E T U f (result.ok t) := result.ok (f t)

definition result.and_then : Π {E T U : Type}, result E T → (T -> result E U) → result E U
| E T U (result.err e) _ := result.err e
| E T U (result.ok t) f := f t

attribute [instance]
definition result_functor (E : Type) : functor (result E) := functor.mk (@result.map E)

definition result.seq : Π {E T U : Type}, result E (T → U) -> result E T → result E U
| E T U f t := result.and_then f (fun f', result.and_then t (fun t', result.ok (f' t')))

-- -- This crashes ....
-- attribute [instance]
-- definition result_applicative (E : Type) : applicative (result E) :=
--   applicative.mk (@result.map E) (@result.ok E) (@result.seq E)

attribute [instance]
definition result_monad (E : Type) : monad (result E) :=
 monad.mk (@result.map E) (@result.ok E) (@result.and_then E)

set_option pp.universes true

-- inductive resultT.{m l} (M : Type.{m} -> Type.{m + 1}) (E A : Type.{l}) : Type.{l + 1}
-- | run : M (result E A) → resultT

-- definition resultT.map {M : Type -> Type} [functor : functor M] : Π {E A B : Type}, (A → B) → resultT M E A → resultT M E B
-- | E A B f (resultT.run action) :=
--   resultT.run $ (@functor.map M functor _ _ (result.map f) action)

-- set_option pp.universes true

-- attribute [instance]
-- definition resultT_functor {M : Type -> Type} [f : functor M] (E : Type) : functor (resultT M E) :=
--     functor.mk (@resultT.map M f E)

end system
