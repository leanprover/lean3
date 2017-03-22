import .syntax

@[reducible] def smt2.builder (A : Type) := state (list smt2.cmd) A

meta def smt2.builder.to_format {A : Type} (build : smt2.builder A) : format :=
    format.join $ list.map to_fmt $ (build [])^.snd

meta instance (A : Type) : has_to_format (smt2.builder A) :=
    ⟨ smt2.builder.to_format ⟩

namespace smt2

namespace builder

def add_command (c : cmd) : builder unit := do
    cs <- state.read,
    state.write (c :: cs)

def echo (msg : string) : builder unit :=
    add_command (cmd.echo msg)

end builder

end smt2
