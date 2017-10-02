universe variables u

structure Functor (A : Type u) :=
(fn : A → A → A) (inj : ∀ x y, fn x = fn y → x = y)

attribute [instance]
definition coe_functor_to_fn (A : Type u) : has_coe_to_fun (Functor A) :=
{ domain := _, codomain := _,
  coe := Functor.fn }

constant f : Functor nat

#check f 0 1

set_option pp.coercions false

#check f 0 1

set_option pp.coercions true

#check f 0 1

set_option pp.all true

#check f 0 1
