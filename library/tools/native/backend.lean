/- We define a backend in Lean to be a function which given the
   fully transformed program, runs an `io` action corresponding
   to whatever compilation steps are required for the particular
   backend. -/

import system.io
import .ir

namespace ir

meta structure backend : Type :=
    -- TODO: we should unify context with the list of items to process
    -- this is just due to the poor design of the compiler
    -- forced into tactic because of universe constraints on io
    (compiler : native.ir.context → tactic unit)

end ir

