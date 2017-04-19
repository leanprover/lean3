import .syntax

@[reducible] def smt2.builder (α : Type) := state (list smt2.cmd) α

meta def smt2.builder.to_format {α : Type} (build : smt2.builder α) : format :=
format.join $ list.intersperse "\n" $ (list.map to_fmt $ (build []).snd).reverse

meta instance (α : Type) : has_to_format (smt2.builder α) :=
⟨ smt2.builder.to_format ⟩

namespace smt2

namespace builder

def equals (t u : term) : term :=
term.apply "=" [t, u]

def not (t : term) : term :=
term.apply "not" [t]

def implies (t u : term) : term :=
term.apply "implies" [t, u]

def forallq (sym : symbol) (s : sort) (t : term) : term :=
term.forallq [(sym, s)] t

def and (ts : list term) : term :=
term.apply "and" ts

def and2 (t u : term) : term :=
and [t, u]

def or (ts : list term) : term :=
term.apply "or" ts

def or2 (t u : term) : term :=
or [t, u]

def iff (t u : term) : term :=
term.apply "iff" [t, u]

def lt (t u : term) : term :=
term.apply "<" [t, u]

def lte (t u : term) : term :=
term.apply "<=" [t, u]

def gt (t u : term) : term :=
term.apply ">" [t, u]

def gte (t u : term) : term :=
term.apply ">=" [t, u]

def add (t u : term) : term :=
term.apply "+" [t, u]

def sub (t u : term) : term :=
term.apply "-" [t, u]

def mul (t u : term) : term :=
term.apply "*" [t, u]

def div (t u : term) : term :=
term.apply "div" [t, u]

def int_const (i : int) : term :=
term.const $ special_constant.number i

def add_command (c : cmd) : builder unit := do
cs ← state.read,
state.write (c :: cs)

def echo (msg : string) : builder unit :=
add_command (cmd.echo msg)

def check_sat : builder unit :=
add_command cmd.check_sat

def pop (n : nat) : builder unit :=
add_command $ cmd.pop n

def push (n : nat) : builder unit :=
add_command $ cmd.push n

def scope {α} (level : nat) (action : builder α) : builder α :=
do push level,
   res ← action,
   pop level,
   return res

def assert (t : term) : builder unit :=
add_command $ cmd.assert_cmd t

def reset : builder unit :=
add_command cmd.reset

def exit' : builder unit :=
add_command cmd.exit_cmd

def declare_const (sym : string) (s : sort) : builder unit :=
add_command $ cmd.declare_const sym s

def declare_fun (sym : string) (ps : list sort) (ret : sort) : builder unit :=
add_command $ cmd.declare_fun sym ps ret

def declare_sort (sym : string) (arity : nat) : builder unit :=
add_command $ cmd.declare_sort sym arity

end builder

end smt2
