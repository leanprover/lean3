prelude
import init.meta.tactic
import init.meta.simp_tactic
import init.meta.defeq_simp_tactic
import init.meta.rewrite_tactic
import init.meta.expr
import init.meta.unfold_tactic
import init.monad
import init.list
import init.combinator
import init.wf
import init.relation
import init.meta.injection_tactic
import init.measurable
import init.applicative

namespace backend

-- A Wadler-style pretty printer

inductive doc :=
| nil
| append : doc → doc → doc
| nest : nat → doc → doc
| text : string → doc
| line : doc
| group : doc → doc → doc

definition doc_size [semireducible] : doc → nat
| doc_size doc.nil := 1
| doc_size (doc.append d1 d2) := 1 + doc_size d1 + doc_size d2
| doc_size (doc.nest _ d) := 1 + doc_size d
| doc_size (doc.text s) := 1
| doc_size doc.line := 1
| doc_size (doc.group d1 d2) := 1 + doc_size d1 + doc_size d2

definition doc_wf [instance] : well_founded (nat.measure doc_size) :=
  nat.measure.wf doc_size

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

definition group (d : doc) := doc.group (flatten d) d

definition sum [reducible] : list nat -> nat
| sum [] := 0
| sum (x :: xs) := x + sum xs

definition list_doc_measure : list (ℕ × doc) → nat :=
  fun xs, sum (list.map (fun x, doc_size (prod.pr2 x)) xs)

definition fits (w : nat) : nat → simple_doc → bool
| fits k simple_doc.nil :=
  if w < k
  then bool.ff
  else bool.tt
| fits k (simple_doc.text s d') :=
  if w < k
  then bool.ff
  else fits (k + list.length s) d'
| fits k (simple_doc.line i d') :=
  if w < k
  then bool.ff
  else bool.tt

definition better (w k : nat) (x y : simple_doc) : simple_doc :=
  bool.cases_on (fits w k x) x y

definition pair_list_doc_measure (p : nat × list (nat × doc)) : nat :=
  list_doc_measure (prod.pr2 p)

definition docpair_wf [instance] : well_founded (nat.measure pair_list_doc_measure) :=
  nat.measure.wf pair_list_doc_measure

-- definition is_simple (d : doc) : Prop :=
--   match d with
--   | doc.nil := true
--   | doc.text _ := true
--   | doc.line := true
--   | _ := false
--   end

-- -- Ideally use wf-recursion to keep the implmentation clean, and generate good code for it.
-- definition be_flatten (n : nat) (d : doc) :  subtype is_simple (list (nat × doc)) :=
--   match d with
--   | doc.nil := []
--   | (doc.append d1 d2) := be' k i d1 ++ be' k i d2
--   | (doc.nest j d) := be' k (i + j) d
--   | (doc.text s) := simple.doc s
--   | (doc.line) :=
--   | (doc.union d1 d2) := (k, [])
--   end

-- definition be' (w : nat) : nat × list (nat × doc) -> simple_doc :=

  -- well_founded.fix
  --   (fun x,
  --     prod.cases_on x
  --       (fun k xs,
  --         list.cases_on xs
  --           (fun x, simple_doc.nil)
  --           (fun h t,
  --             (prod.cases_on h
  --               (fun i d,
  --                 doc.cases_on d
  --                   (fun (rec : Π y, nat.measure pair_list_doc_measure y (k, (i, d) :: t) -> simple_doc), rec ((k, t))
  --                     (by sorry))
  --                   (fun x y rec, rec (k, (i, x) :: (i, y) :: t) (by sorry))
  --                   (fun j x rec, rec (k, (i + j, x) :: t) (by sorry))
  --                   (fun s rec, simple_doc.text s (rec (k, t) (by sorry)))
  --                   (fun rec, simple_doc.line i (rec (i, t) (by sorry)))
  --                   (fun x y rec, better w k
  --                     (rec (k, (i, x) :: t) (by sorry))
  --                     (rec (k, (i, y) :: t) (by sorry)))
  --                     ))))) x

-- definition be (w k : nat) (l : list (nat × doc)) : simple_doc :=
--   be' w (k, l)
--   -- | _ := simple_doc.nil
--   -- end

-- definition best (w k : nat) (d : doc) : simple_doc :=
--    be w k [(0, x)]

meta_definition compiler (e : expr) : string := to_string e

end backend
