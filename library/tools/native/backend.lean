/- We define a backend in Lean to be a function which given the
   fully transformed program, runs an `io` action corresponding
   to whatever compilation steps are required for the particular
   backend. -/

import system.io
import .ir

namespace native

meta structure backend : Type :=
    -- TODO: we should unify context with the list of items to process
    -- this is just due to the poor design of the compiler
    -- forced into tactic because of universe constraints on io
    (compiler : native.ir.context → tactic unit)
    (name : string)

meta def backend.to_string (b : backend) : string := b.name

meta instance backend_has_to_string : has_to_string backend :=
⟨ fun b, b.to_string ⟩

end native

