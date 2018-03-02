set_option pp.implicit true

structure C :=
( d : Π { X : Type }, list X → list X )

def P(c : C):= c.d [0]

#print P

structure D (α : Type) :=
(d : α)

#check λ (d : D ℕ), d.d

class E (α : Type) :=
(e : α)

#check λ [E ℕ], E.e ℕ
