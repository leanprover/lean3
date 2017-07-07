structure Category :=
  ( Obj : Type )
    
definition EmptyCategory : Category := ⟨ empty ⟩ 

structure Functor ( C : Category ) ( D : Category ) :=
  ( onObjects   : C.Obj → D.Obj )

definition EmptyFunctor ( C : Category ) : Functor EmptyCategory C := 
begin
  split,
  intros,
  trace_state,
  unfold_projs at * {md:=semireducible},
  trace_state,
  induction a
end