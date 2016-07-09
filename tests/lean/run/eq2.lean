definition symm {A : Type} : Π {a b : A}, a = b → b = a
| a a (eq.refl a) := rfl

definition trans {A : Type} : Π {a b c : A}, a = b → b = c → a = c
| a a a (eq.refl a) (eq.refl a) := rfl
