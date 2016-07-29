prelude
import init.meta.tactic
import init.meta.simp_tactic
import init.meta.defeq_simp_tactic
import init.meta.expr
import init.meta.unfold_tactic
import init.monad
import init.list
import init.combinator
import init.wf
import init.relation
import init.meta.injection_tactic
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

inductive induction_target :=
| expr : expr -> induction_target
| name : name → induction_target

definition expr_to_induction_target [coercion] (e : expr) : induction_target :=
  induction_target.expr e

definition name_to_induction_target [coercion] (n : name) : induction_target :=
  induction_target.name n

definition string_to_induction_target [coercion] (s : string) : induction_target :=
  induction_target.name s

meta_definition induction_on (target : induction_target) : tactic unit := do
  H <- (match target with | induction_target.name n := tactic.get_local n
                          | induction_target.expr e := return e
                          end),
  t <- tactic.infer_type H,
  let type_sym := expr.get_app_fn t in
  let type_name := expr.const_name type_sym in
  tactic.induction_core tactic.transparency.semireducible H (type_name <.> "rec_on") ["x1", "x2"]

-- meta_definition mk_const_motif (t : expr) (n : name) : tactic expr :=
--   pure (expr.lam "a" binder_info.default t) <*> (tactic.mk_const n)

-- definition be (w : nat) (thing : nat × list (nat × doc)) : simple_doc :=
--   by do tactic.intros,
--         let A := tactic.mk_const "doc" in
--         motif <- mk_const_motif A (tactic.mk_const "simple_doc") in
--         tactic.mk_mapp ("well_founded" <.> "recursion") [some A, none, some motif, none, none, none] >>= tactic.fapply,
--         return unit.star

open tactic

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

-- meta_definition compute : tactic unit :=
-- by do
--   tgt <- target,
--   match expr.is_app tgt with
--   | bool.ff := return unit.star
--   | bool.tt :=
--     let fn := expr.app_fn tgt
--     in match expr.is_constant fn with
--     | bool.ff := return unit.star
--     | bool.tt := do
--       unfold [expr.const_name fn],
--       dsimp,
--       return unit.star
--     end
--   end

definition docpair_wf [instance] : well_founded (nat.measure pair_list_doc_measure) :=
  nat.measure.wf pair_list_doc_measure

-- check list.map

-- theorem simp_rule :
--   forall A B (f : A -> B), list.map f [] = [] :=
--   by do intros, return unit.star

-- theorem tail_measure_always_lt_list :
--   forall x xs k, nat.measure pair_list_doc_measure (k, xs) (k, x :: xs) :=
-- by do
-- intro `x,
-- intro `xs,
-- induction_on `xs,
-- intros,
-- unfold [`backend.pair_list_doc_measure, `nat.measure, `inv_image, `backend.list_doc_measure],
-- unfold [`backend.doc_size],
-- unfold [`init.list.map],
-- dsimp,
-- return unit.star

-- definition be' (w : nat) (x : nat × list (nat × doc)) : simple_doc :=
--   well_founded.fix
--     (fun x,
--       prod.cases_on x
--         (fun k xs,
--           list.cases_on xs
--             (fun x, simple_doc.nil)
--             (fun h t,
--               (prod.cases_on h
--                 (fun i d,
--                   doc.cases_on d
--                     (fun (rec : Π y, nat.measure pair_list_doc_measure y (k, (i, d) :: t) -> simple_doc), rec ((k, t))
--                       (by do return unit.star))
--                       -- compute, unfold ["nat" <.> "measure", "inv_image", "backend" <.> "pair_list_doc_measure", "backend" <.> "list_doc_measure","nat" <.> "measure"], dsimp, return unit.star))
--                     (fun x y rec, rec (k, (i, x) :: (i, y) :: t) (by return unit.star))
--                     (fun j x rec, rec (k, (i + j, x) :: t) (by return unit.star))
--                     (fun s rec, simple_doc.text s (rec (k, t) (by return unit.star)))
--                     (fun rec, simple_doc.line i (rec (i, t) (by return unit.star)))
--                     (fun x y rec, better w k
--                       (rec (k, (i, x) :: t) (by return unit.star))
--                       (rec (k, (i, y) :: t) (by return unit.star))
--                       )))))) x

-- definition be (w k : nat) (l : list (nat × doc)) : simple_doc :=
--   be' w (k, l)
--   -- | _ := simple_doc.nil
--   -- end

-- definition best (w k : nat) (d : doc) : simple_doc :=
--    be w k [(0, x)]

meta_definition compiler (e : expr) : string :=
   to_string e

end backend
