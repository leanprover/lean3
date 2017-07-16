open tactic

constant α : Type
constant a : α
axiom f : ∀ b : α, a = b
theorem g (b : α) : b = a := eq.symm (f b)

run_cmd list_axioms `g >>= trace
#print axioms g

run_cmd list_axioms `nat.add_comm >>= trace
#print axioms nat.add_comm

run_cmd list_axioms `fake_name
#print axioms fake_name
