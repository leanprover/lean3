-- TODO(dhs, leo): if `iff` is set to be reducible, then `not_false_iff` becomes
-- an invalid [simp] rule. Right now we throw an error when blast starts, though in the
-- future we may just wish to ignore [simp] rules that are no longer valid.
--attribute iff [reducible]
set_option blast.strategy "ematch"

definition lemma1 (p : nat → Prop) (a b c : nat) : p a → a = b → p b :=
by blast

set_option pp.beta true
print lemma1
