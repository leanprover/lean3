universe variables u v

structure Func :=
(A : Type u) (B : A → Type v) (fn : Π a, B a → B a)

instance F_to_fn : has_coe_to_fun Func :=
{ domain := _, codomain := _,
  coe := λ f, f^.fn }

variables (f : Func) (a : f^.A) (b : f^.B a)
#check (f a b)
