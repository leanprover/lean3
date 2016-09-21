namespace system

-- I'm extending the stdlib tho, which is good, we now have a system.result 
inductive {e r} result (E : Type e) (R : Type r) : Type (max 1 e r)
| err {} : E -> result
| ok {} : R -> result

-- TODO: elaborator is still underway, eventually clean these up, hacking around elab bugs
definition unwrap_or {E T : Type*} : result E T -> T -> T
| (result.err _) default := default
| (result.ok t) _ := t

definition result.map : Π {E : Type*} {T : Type*} {U : Type*}, (T → U) → result E T → result E U
| E T U f (result.err e) := result.err e
| E T U f (result.ok t) := result.ok (f t)

definition result.and_then {E T U : Type*} : result E T → (T -> result E U) → result E U
| (result.err e) _ := result.err e
| (result.ok t) f := f t

attribute [instance]
definition result_functor (E : Type*) : functor (result E) := functor.mk (@result.map E)

definition result.seq {E T U : Type*} : result E (T → U) -> result E T → result E U
| f t := result.and_then f (fun f', result.and_then t (fun t', result.ok (f' t')))

attribute [instance]
definition result_applicative (E : Type) : applicative (result E) :=
  applicative.mk (@result.map E) (@result.ok E) (@result.seq E)

attribute [instance]
definition result_monad (E : Type) : monad (result E) :=
 monad.mk (@result.map E) (@result.ok E) (@result.and_then E)

inductive {u v w} resultT (M : Type (max 1 u w) -> Type v) (E : Type u) (A : Type w) : Type (max 1 u v)
| run : M (result E A) → resultT

section resultT
  universe variables u v w

  variable {M : Type (max 1 v u) -> Type w}

  definition resultT.map [functor : functor M] {E : Type v} {A B : Type u} : (A → B) → resultT M E A → resultT M E B
  | f (resultT.run action) := resultT.run $ (@functor.map M functor _ _ (result.map f) action)

  definition resultT.pure [monad : monad M] {E A : Type*} (x : A) : resultT M E A :=
    resultT.run $ return (result.ok x)

  definition resultT.and_then [monad : monad M] {E A B : Type*} : resultT M E A → (A → resultT M E B) → resultT M E B
  | (resultT.run action) f := resultT.run $ (do
  res_a <- action,
  -- a little ugly with this match
  (match res_a with
  | system.result.err e := return (system.result.err e)
  | system.result.ok a := let (resultT.run actionB) := f a in actionB
  end : M (result E B)))

  attribute [instance]
  definition resultT_functor [f : functor M] (E : Type*) : functor (resultT M E) :=
    functor.mk (@resultT.map M f E)

  -- Should we unify functor and monad like haskell? 
  attribute [instance]
  definition resultT_monad {M : Type* -> Type*} [f : functor M] [m : monad M] (E : Type*) : monad (resultT M E) :=
    monad.mk (@resultT.map M f E) (@resultT.pure M m E) (@resultT.and_then M m E)
end resultT

end system
