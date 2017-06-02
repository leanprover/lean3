/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering init.coe

/- Reflect a C++ name object. The VM replaces it with the C++ implementation. -/
inductive name
| anonymous  : name
| mk_string  : string → name → name
| mk_numeral : unsigned → name → name

/-- Gadget for automatic parameter support. This is similar to the opt_param gadget, but it uses
    the tactic declaration names tac_name to synthesize the argument.
    Like opt_param, this gadget only affects elaboration.
    For example, the tactic will *not* be invoked during type class resolution. -/
@[reducible] def {u} auto_param (α : Sort u) (tac_name : name) : Sort u :=
α

instance : inhabited name :=
⟨name.anonymous⟩

def mk_str_name (n : name) (s : string) : name :=
name.mk_string s n

def mk_num_name (n : name) (v : nat) : name :=
name.mk_numeral (unsigned.of_nat' v) n

def mk_simple_name (s : string) : name :=
mk_str_name name.anonymous s

instance string_to_name : has_coe string name :=
⟨mk_simple_name⟩

infix ` <.> `:65 := mk_str_name

open name

def name.get_prefix : name → name
| anonymous        := anonymous
| (mk_string s p)  := p
| (mk_numeral s p) := p

def name.update_prefix : name → name → name
| anonymous        new_p := anonymous
| (mk_string s p)  new_p := mk_string s new_p
| (mk_numeral s p) new_p := mk_numeral s new_p

def name.to_string_with_sep (sep : string) : name → string
| anonymous                := "[anonymous]"
| (mk_string s anonymous)  := s
| (mk_numeral v anonymous) := to_string v
| (mk_string s n)          := name.to_string_with_sep n ++ sep ++ s
| (mk_numeral v n)         := name.to_string_with_sep n ++ sep ++ to_string v

private def name.components' : name -> list name
| anonymous                := []
| (mk_string s n)          := mk_string s anonymous :: name.components' n
| (mk_numeral v n)         := mk_numeral v anonymous :: name.components' n

def name.components (n : name) : list name :=
(name.components' n).reverse

def name.to_string : name → string :=
name.to_string_with_sep "."

instance : has_to_string name :=
⟨name.to_string⟩

instance name.has_decidable_eq : decidable_eq name
| anonymous        anonymous          := is_true rfl
| anonymous        (mk_string s' p')  := is_false (λh, name.no_confusion h)
| anonymous        (mk_numeral s' p') := is_false (λh, name.no_confusion h)
| (mk_string s p)  anonymous          := is_false (λh, name.no_confusion h)
| (mk_string s p)  (mk_string s' p')  := if ss : s = s' then
  @dite _ (name.has_decidable_eq p p') _
    (λpp, is_true $ congr (congr_arg mk_string ss) pp)
    (λpp, is_false $ λh, name.no_confusion h (λ_, pp))
  else is_false $ λh, name.no_confusion h (λn _, ss n)
| (mk_string s p)  (mk_numeral s' p') := is_false (λh, name.no_confusion h)
| (mk_numeral s p) anonymous          := is_false (λh, name.no_confusion h)
| (mk_numeral s p) (mk_string s' p')  := is_false (λh, name.no_confusion h)
| (mk_numeral s p) (mk_numeral s' p') := if ss : s = s' then
  @dite _ (name.has_decidable_eq p p') _
    (λpp, is_true $ congr (congr_arg mk_numeral ss) pp)
    (λpp, is_false $ λh, name.no_confusion h (λ_, pp))
  else is_false $ λh, name.no_confusion h (λn _, ss n)

/- Both cmp and lex_cmp are total orders, but lex_cmp implements a lexicographical order. -/
def name.lex_cmp : name → name → ordering
| anonymous        anonymous          := ordering.eq
| anonymous        _                  := ordering.lt
| _                anonymous          := ordering.gt
| (mk_string s p)  (mk_string s' p')  := (has_ordering.cmp s s').or_else (name.lex_cmp p p')
| (mk_string s p)  (mk_numeral s' p') := ordering.gt
| (mk_numeral s p) (mk_string s' p')  := ordering.lt
| (mk_numeral s p) (mk_numeral s' p') := (has_ordering.cmp s s').or_else (name.lex_cmp p p')

meta constant name.cmp : name → name → ordering

def name.append (n1 : name) : name → name
| anonymous          := n1
| (mk_string s2 n2)  := mk_string s2 (name.append n2)
| (mk_numeral s2 n2) := mk_numeral s2 (name.append n2)

def name.is_internal : name → bool
| anonymous        := ff
| (mk_string s n)  := if list.head s = '_' then tt else name.is_internal n
| (mk_numeral s n) := name.is_internal n

meta instance : has_ordering name :=
⟨name.cmp⟩

instance : has_append name :=
⟨name.append⟩

/- (name.append_after n i) returns a name of the form n_i -/
def name.append_after : name → nat → name
| (mk_string s n) i := n <.> (s ++ "_" ++ to_string i)
| n               i := n <.> ("_" ++ to_string i)

def name.is_prefix_of : name → name → bool
| p name.anonymous   := ff
| p (mk_string s n)  := if p = n then tt else name.is_prefix_of p n
| p (mk_numeral v n) := if p = n then tt else name.is_prefix_of p n

def name.replace_prefix : name → name → name → name
| anonymous        p p' := anonymous
| (mk_string s c)  p p' := if c = p then mk_string s p' else mk_string s (name.replace_prefix c p p')
| (mk_numeral v c) p p' := if c = p then mk_numeral v p' else mk_numeral v (name.replace_prefix c p p')
