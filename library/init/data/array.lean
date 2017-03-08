/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat init.data.list.lemmas
universes u w

structure array (α : Type u) (n : nat) :=
(data : fin n → α)

def mk_array {α} (n) (v : α) : array α n :=
{data := λ _, v}

namespace array
variables {α : Type u} {β : Type w} {n : nat}

def nil {α} : array α 0 :=
{data := λ ⟨x, h⟩, absurd h (nat.not_lt_zero x)}

def read (a : array α n) (i : fin n) : α :=
a^.data i

def read' [inhabited α] (a : array α n) (i : nat) : α :=
if h : i < n then a^.read ⟨i,h⟩ else default α

def write (a : array α n) (i : fin n) (v : α) : array α n :=
{data := λ j, if i = j then v else a^.read j}

def write' (a : array α n) (i : nat) (v : α) : array α n :=
if h : i < n then a^.write ⟨i, h⟩ v else a

lemma push_back_idx {j n} (h₁ : j < n + 1) (h₂ : j ≠ n) : j < n :=
nat.lt_of_le_and_ne (nat.le_of_lt_succ h₁) h₂

def push_back (a : array α n) (v : α) : array α (n+1) :=
{data := λ ⟨j, h₁⟩, if h₂ : j = n then v else a^.read ⟨j, push_back_idx h₁ h₂⟩}

lemma pop_back_idx {j n} (h : j < n) : j < n + 1 :=
nat.lt.step h

def pop_back (a : array α (n+1)) : array α n :=
{data := λ ⟨j, h⟩, a^.read ⟨j, pop_back_idx h⟩}

lemma lt_aux_1 {a b c : nat} (h : a + c < b) : a < b :=
lt_of_le_of_lt (nat.le_add_right a c) h

lemma lt_aux_2 {n} (h : n > 0) : n - 1 < n :=
have h₁ : 1 > 0, from dec_trivial,
nat.sub_lt h h₁

lemma lt_aux_3 {n i} (h : i < n) : n - 1 - i < n := begin
  rw nat.sub_sub,
  apply nat.sub_lt,
  apply lt_of_lt_of_le (nat.zero_lt_succ _) h,
  rw add_comm,
  apply nat.zero_lt_succ
end

def foreach_aux (f : fin n → α → α) : Π (i : nat), i ≤ n → array α n → array α n
| 0     h a := a
| (j+1) h a :=
  let i : fin n := ⟨n - 1 - j, lt_aux_3 h⟩ in
  foreach_aux j (le_of_lt h) (a^.write i (f i (a^.read i)))

def foreach {n} (a : array α n) (f : fin n → α → α) : array α n :=
foreach_aux f n (le_refl _) a

def map {α} {n} (f : α → α) (a : array α n) : array α n :=
foreach a (λ _, f)

def map₂ {α} {n} (f : α → α → α) (a b : array α n) : array α n :=
foreach b (λ i, f (a^.read i))

def iterate_aux (f : fin n → α → β → β) : Π (i : nat), i ≤ n → array α n → β → β
| 0     h a b := b
| (j+1) h a b :=
  let i : fin n := ⟨n - 1 - j, lt_aux_3 h⟩ in
  iterate_aux j (le_of_lt h) a (f i (a^.read i) b)

def iterate {n} (a : array α n) (b : β) (fn : fin n → α → β → β) : β :=
iterate_aux fn n (le_refl _) a b

def foldl {n} (a : array α n) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

def rev_iterate_aux (f : fin n → α → β → β) : Π (i : nat), i ≤ n → array α n → β → β
| 0     h a b := b
| (j+1) h a b :=
  let i : fin n := ⟨j, h⟩ in
  rev_iterate_aux j (le_of_lt h) a (f i (a^.read i) b)

def rev_iterate {n : nat} (a : array α n) (b : β) (fn : fin n → α → β → β) : β :=
rev_iterate_aux fn n (le_refl _) a b

def to_list (a : array α n) : list α :=
a^.rev_iterate [] (λ _ v l, v :: l)

instance [has_to_string α] : has_to_string (array α n) :=
⟨to_string ∘ to_list⟩

meta instance [has_to_format α] : has_to_format (array α n) :=
⟨to_fmt ∘ to_list⟩

meta instance [has_to_tactic_format α] : has_to_tactic_format (array α n) :=
⟨tactic.pp ∘ to_list⟩

end array

def list.to_array {α} (l : list α) : array α l^.length :=
{data := λ ⟨j, h⟩, l^.nth_le j h}
