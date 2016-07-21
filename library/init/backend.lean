prelude
import init.meta.expr

namespace backend

inductive doc :=
  | nil
  | append : doc → doc → doc
  | nest : nat → doc → doc
  | text : string → doc
  | line : doc
  | group : doc → doc → doc

inductive simple_doc :=
  | nil
  | text : string → simple_doc → simple_doc
  | line : nat → simple_doc → simple_doc

definition empty : doc :=
  doc.nil

definition concat (a b : doc) : doc :=
  doc.append a b

definition nest (n : nat) (d : doc) :=
  doc.nest n d

definition text (s : string) :=
  doc.text s

definition line := doc.line

definition flatten : doc → doc
| flatten doc.nil := doc.nil
| flatten (doc.append x y) :=
  doc.append (flatten x) (flatten y)
| flatten (doc.nest n x) :=
  doc.nest n (flatten x)
| flatten (doc.text s) := doc.text s
| flatten doc.line := doc.text " "
| flatten (doc.group x y) :=
  flatten x

definition repeat {A} : nat -> A -> list A
| repeat 0 x := []
| repeat (nat.succ n) x := repeat n x

definition layout : simple_doc → string
| layout simple_doc.nil := ""
| layout (simple_doc.text s d) := s ++ layout d
| layout (simple_doc.line i x) := '\n' :: (repeat i ' ' ++ layout x)

definition group (d : doc) :=
  doc.group (flatten d) d

print inductive expr

meta_definition compiler (e : expr) : string :=
   to_string e

end backend
