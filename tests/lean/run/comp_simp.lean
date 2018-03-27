#print [comp_simp] -- simplification lemmas for the compiler

@[inline] def f (a : list nat) : list nat :=
list.map (+1) (list.map (*2) a)

#print f._comp_simp -- summary for `f` after simplification and inlining

def g (a : list nat) : list nat :=
f (list.map (+2) a)

#print g._comp_simp -- summary for `g` after simplification and inlining
