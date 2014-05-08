-- Hurkens' paradox in lean

import macros
import tactic

definition app {A B : Type} (f : A → B) (x : A) : B := (f x).

infix 1 $ : app.

variable large : Bool.

variable False : Bool.

variable inj : ∀ A : Bool, large.

variable proj : large → Bool.

axiom proj_ax : ∀ A : Bool, proj (inj A) = A.

definition V := ∀ A : Bool, ( (A → large) → A → large ) → A → large.
definition U := V → large.

definition sb (z : V) : V := fun A r a, r (z A r) a.

definition le (i : U → large) (x : U) : large :=
           x (fun A r a, i (fun v, sb v A r a)).

infix 20 ⊂ : le

definition induct (i : U → large) : large :=
           inj $ ∀ x : U, proj (i ⊂ x) → proj (i x).

definition WF : U := fun z, induct (z U le).

definition I (x : U) : large :=
           inj $
           (∀ i : U → large, proj (le i x) → proj (i (fun v, sb v U le x))) → False.

check @subst.

check proj (inj False).

variable P : Bool -> Bool.
axiom toto : P (proj (inj False)).

check (subst toto (proj_ax False)).

axiom Abort {P : Bool} : P.

definition ord_up_to := fun (a : U) (v : V), sb v U le a

-- This was painful
theorem Omega : ∀ i : U → large, proj (induct i) → proj (i WF)
:=
        assume i : U → large,
        assume i_ind : proj (induct i),
        have i_ind_defn : ∀ x : U, proj (i ⊂ x) → proj (i x), from
             subst i_ind (proj_ax _),
        have proj_leq_wf : proj (i⊂WF) , from (
             have H : ∀ x : U, proj ((fun a : U, i (fun v : V, ord_up_to a v)) ⊂ x) → proj (i (ord_up_to x)),
             from (
                  assume x : U,
                  assume H1 : proj ((fun a : U, i (ord_up_to a)) ⊂ x),
                  show proj (i (ord_up_to x)), from (i_ind_defn (fun v : V, ord_up_to x v) H1)
             ),
         subst H (symm (proj_ax _))
         ),
        i_ind_defn _ proj_leq_wf



theorem lemma1 : proj (induct I)
:= have H : ∀ x : U, proj (I ⊂ x) → proj (I x), from (
        assume x : U,
        assume P : proj (I ⊂ x),
        show proj (inj ((∀ i : U → large, proj (i ⊂ x) → proj (i (ord_up_to x))) → False)), from
               have H1 : (∀ i : U → large, proj (i ⊂ x) → proj (i (ord_up_to x))) → False, from (
                    assume Q : ∀ i : U → large, proj (i ⊂ x) → proj (i (ord_up_to x)),
                    have H : proj (I (ord_up_to x)), from Q I P,
                    have H2 : (∀ i : U → large, proj (i ⊂ ord_up_to x) → proj (i (ord_up_to (ord_up_to x))))
                    → False, from (subst H (proj_ax _)),
                    H2 (fun i : U → large, Q (fun a, i (ord_up_to a)))),
        subst H1 (symm (proj_ax _))),
   subst H (symm (proj_ax _))

theorem lemma2 : (∀ i, proj (induct i) → proj (i WF)) → False
:=
   assume P,
   have H : proj (I WF), from (P I lemma1),
   have H1 : (∀ i : U → large, proj (i ⊂ WF) → proj (i (ord_up_to WF))) → False, from (subst H (proj_ax _)),
   let H2 :=
       assume i : U → large,
       let H0 := P (fun a, i (ord_up_to a)) in
       assume H3 : proj (i ⊂ WF),
       H0 H3 in
   H1 H2

theorem contr : False
:= lemma2 Omega.