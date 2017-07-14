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

namespace backend

meta def unpack_items : list ir.item → (list ir.defn × list ir.decl × list ir.type_decl)
| [] := ([], [], [])
| (i :: is) :=
  let (defs, decls, types) := unpack_items is in
  match i with
  | ir.item.defn d := (d :: defs, decls, types)
  | ir.item.decl d := (defs, d :: decls, types)
  | ir.item.type td := (defs, decls, td :: types)
  end

end backend

end native

