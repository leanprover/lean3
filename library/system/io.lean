
 /- TODO @lukenels: Separate this monad stuff out of here -/
 structure functor [class] (f : Type → Type) : Type :=
 (map : Π {a b: Type}, (a → b) → f a → f b)

 structure monad [class] (m : Type → Type) extends functor m : Type :=
 (return : Π {a:Type}, a → m a)
 (bind : Π {a b: Type}, m a → (a → m b) → m b)

 constant RealWorld : Type

 structure IO (a : Type) : Type :=
 (runIO : RealWorld → a × RealWorld)

 definition functorIO [instance] : functor IO :=
 {| functor IO,
    map := λ (a b: Type) (f: a → b) (x: IO a),
    IO.mk (λ rw, match IO.runIO x rw with
                 prod.mk res rw' := prod.mk (f res) rw'
                 end)
 |}

 definition monadIO [instance] : monad IO :=
 {| monad IO,
    functorIO,
    return := λ (T:Type) (x:T),
      IO.mk (λ rw, prod.mk x rw),
    bind := λ (a b: Type) (x: IO a) (f: a → IO b),
      IO.mk (λ rw,
        match IO.runIO x rw with
        prod.mk res rw' := IO.runIO (f res) rw'
        end)
 |}

