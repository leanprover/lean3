def my_list := list ℕ
variable (l : my_list)
example := ∀ x ∈ (l : list ℕ), x > 3
             -- ^ should use has_mem instance for lists here

def frob := (l : list ℕ)
-- inferred type of frob should be my_list → list ℕ
open tactic run_cmd do
t ← infer_type ```(frob l),
guard $ t = ```(list ℕ)

class foo (α : Type) := (u : unit)
def my_unit := unit
instance : foo my_unit := ⟨_, ()⟩
def gadget {α} (x : α) [foo α] : Type := unit
example : gadget (() : my_unit) := ()
               -- ^^ type class inference should be invoked for `foo my_unit` here
