/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
prelude
import init.data.list.basic init.function init.meta init.data.nat.lemmas
import init.meta.interactive init.meta.smt.rsimp

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace list
open nat

/- append -/

@[simp] lemma nil_append (s : list α) : [] ++ s = s :=
rfl

@[simp] lemma cons_append (x : α) (s t : list α) : (x::s) ++ t = x::(s ++ t) :=
rfl

@[simp] lemma append_nil (t : list α) : t ++ [] = t :=
by induction t; simph

@[simp] lemma append_assoc (s t u : list α) : s ++ t ++ u = s ++ (t ++ u) :=
by induction s; simph

lemma append_ne_nil_of_ne_nil_left (s t : list α) : s ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

lemma append_ne_nil_of_ne_nil_right (s t : list α) : t ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

lemma append_foldl (f : α → β → α) (a : α) (s t : list β) : foldl f a (s ++ t) = foldl f (foldl f a s) t :=
by {revert a, induction s with b s H, exact λ_, rfl, intros, simp[foldl], rw H _}

lemma append_foldr (f : α → β → β) (a : β) (s t : list α) : foldr f a (s ++ t) = foldr f (foldr f a t) s :=
by {revert a, induction s with b s H, exact λ_, rfl, intros, simp[foldr], rw H _}

/- concat -/

@[simp] lemma concat_eq_append (a : α) (l : list α) : concat l a = l ++ [a] :=
by induction l; simph [concat]

/- head & tail -/

attribute [simp] head tail

@[simp] lemma head_append [h : inhabited α] (t : list α) {s : list α} (h : s ≠ []) : head (s ++ t) = head s :=
by {induction s, contradiction, simp}

lemma cons_head_tail [h : inhabited α] {l : list α} (h : l ≠ []) : (head l)::(tail l) = l :=
by {induction l, contradiction, simp}

@[simp] lemma length_tail (l : list α) : length (tail l) = length l - 1 :=
by cases l; refl

/- repeat taken dropn -/

attribute [simp] repeat taken dropn

/- length -/

attribute [simp] length

lemma length_cons (a : α) (l : list α) : length (a :: l) = length l + 1 :=
rfl

@[simp] lemma length_append (s t : list α) : length (s ++ t) = length s + length t :=
by induction s; simph

lemma length_concat (a : α) (l : list α) : length (concat l a) = succ (length l) :=
by simp [succ_eq_add_one]

@[simp] lemma length_repeat (a : α) (n : ℕ) : length (repeat a n) = n :=
by induction n; simph; refl

lemma eq_nil_of_length_eq_zero {l : list α} : length l = 0 → l = [] :=
by {induction l; intros, refl, contradiction}

lemma ne_nil_of_length_eq_succ {l : list α} : ∀ {n : nat}, length l = succ n → l ≠ [] :=
by induction l; intros; contradiction

-- TODO(Leo): cleanup proof after arith dec proc
@[simp] lemma length_taken : ∀ (i : ℕ) (l : list α), length (taken i l) = min i (length l)
| 0        l      := by simp
| (succ n) []     := by simp
| (succ n) (a::l) := begin simph [nat.min_succ_succ, add_one_eq_succ] end

-- TODO(Leo): cleanup proof after arith dec proc
@[simp] lemma length_dropn : ∀ (i : ℕ) (l : list α), length (dropn i l) = length l - i
| 0 l         := rfl
| (succ i) [] := eq.symm (nat.zero_sub_eq_zero (succ i))
| (succ i) (x::l) := calc
  length (dropn (succ i) (x::l))
          = length l - i             : length_dropn i l
      ... = succ (length l) - succ i : nat.sub_eq_succ_sub_succ (length l) i

lemma length_drop : ∀ (i : ℕ) (l : list α), i < length l → length (drop i l) = length l - 1
| 0        l      h := length_tail _
| (succ i) []     h := by simp [drop]
| (succ i) (x::l) h := have i < length l, from lt_of_succ_lt_succ h,
  by dsimp [drop]; rw [length_drop i l this, nat.sub_add_cancel (lt_of_le_of_lt (nat.zero_le _) this)]; refl
/- nth -/

theorem nth_le_nth : Π (l : list α) (n h), l^.nth n = some (l^.nth_le n h)
| []       n     h := absurd h (not_lt_zero n)
| (a :: l) 0     h := rfl
| (a :: l) (n+1) h := nth_le_nth l n _

theorem nth_ge_len : Π (l : list α) (n), n ≥ l^.length → l^.nth n = none
| []       n     h := rfl
| (a :: l) 0     h := absurd h (not_lt_zero _)
| (a :: l) (n+1) h := nth_ge_len l n (le_of_succ_le_succ h)

theorem ext : Π {l₁ l₂ : list α}, (∀n, l₁^.nth n = l₂^.nth n) → l₁ = l₂
| []      []       h := rfl
| (a::l₁) []       h := by note h0 := h 0; contradiction
| []      (a'::l₂) h := by note h0 := h 0; contradiction
| (a::l₁) (a'::l₂) h := by assertv h0 : some a = some a' := h 0; injection h0 with aa; simph[ext $ λn, h (n+1)]

theorem ext_le {l₁ l₂ : list α} (hl : l₁^.length = l₂^.length) (h : ∀n h₁ h₂, l₁^.nth_le n h₁ = l₂^.nth_le n h₂) : l₁ = l₂ :=
ext $ λn, if h₁ : n < l₁^.length
  then by rw [nth_le_nth, nth_le_nth, h n h₁ (by rwa -hl)]
  else let h₁ := le_of_not_gt h₁ in by rw [nth_ge_len _ _ h₁, nth_ge_len _ _ (by rwa -hl)]

/- map -/

attribute [simp] map

lemma map_cons (f : α → β) (a l) : map f (a::l) = f a :: map f l :=
rfl

@[simp] lemma map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = (map f l₁) ++ (map f l₂) :=
by intro l₁; induction l₁; intros; simph

lemma map_singleton (f : α → β) (a : α) : map f [a] = [f a] :=
rfl

lemma map_concat (f : α → β) (a : α) (l : list α) : map f (concat l a) = concat (map f l) (f a) :=
by induction l; simph

@[simp] lemma map_id (l : list α) : map id l = l :=
by induction l; simph

lemma map_id' {f : α → α} (h : ∀ x, f x = x) (l : list α) : map f l = l :=
by induction l; simph

@[simp] lemma map_map (g : β → γ) (f : α → β) (l : list α) : map g (map f l) = map (g ∘ f) l :=
by induction l; simph

@[simp] lemma length_map (f : α → β) (l : list α) : length (map f l) = length l :=
by induction l; simph

@[simp] lemma foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : list β) : foldl f a (map g l) = foldl (λx y, f x (g y)) a l :=
by revert a; induction l; intros; simph[foldl]

@[simp] lemma foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : list β) : foldr f a (map g l) = foldr (f ∘ g) a l :=
by revert a; induction l; intros; simph[foldr]

theorem foldl_hom (f : α → β) (g : α → γ → α) (g' : β → γ → β) (a : α)
  (h : ∀a x, f (g a x) = g' (f a) x) (l : list γ) : f (foldl g a l) = foldl g' (f a) l :=
by revert a; induction l; intros; simph[foldl]

theorem foldr_hom (f : α → β) (g : γ → α → α) (g' : γ → β → β) (a : α)
  (h : ∀x a, f (g x a) = g' x (f a)) (l : list γ) : f (foldr g a l) = foldr g' (f a) l :=
by revert a; induction l; intros; simph[foldr]

/- map₂ -/

attribute [simp] map₂

@[simp] lemma length_map₂ (f : α → β → γ) (l₁) : ∀ l₂, length (map₂ f l₁ l₂) = min (length l₁) (length l₂) :=
by {induction l₁; intro l₂; cases l₂; simph [add_one_eq_succ, min_succ_succ]}

/- reverse -/

@[simp] lemma reverse_nil : reverse (@nil α) = [] :=
rfl

local attribute [simp] reverse_core

@[simp] lemma reverse_cons (a : α) (l : list α) : reverse (a::l) = concat (reverse l) a :=
have aux : ∀ l₁ l₂, reverse_core l₁ (concat l₂ a) = concat (reverse_core l₁ l₂) a,
  by intros l₁; induction l₁; intros; rsimp,
aux l nil

@[simp] lemma reverse_singleton (a : α) : reverse [a] = [a] :=
rfl

@[simp] lemma reverse_append (s t : list α) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
by induction s; simph

@[simp] lemma reverse_reverse (l : list α) : reverse (reverse l) = l :=
by induction l; simph

lemma concat_eq_reverse_cons (a : α) (l : list α) : concat l a = reverse (a :: reverse l) :=
by induction l; simph

@[simp] lemma length_reverse (l : list α) : length (reverse l) = length l :=
by induction l; simph

@[simp] lemma map_reverse (f : α → β) (l : list α) : map f (reverse l) = reverse (map f l) :=
by induction l; simph

lemma nth_le_reverse_aux1 : Π (l r : list α) (i h1 h2), nth_le (reverse_core l r) (i + length l) h1 = nth_le r i h2
| []       r i := λh1 h2, rfl
| (a :: l) r i := by rw (show i + length (a :: l) = i + 1 + length l, by simp); exact
  λh1 h2, nth_le_reverse_aux1 l (a :: r) (i+1) h1 (succ_lt_succ h2)

lemma nth_le_reverse_aux2 : Π (l r : list α) (i : nat) (h1) (h2),
  nth_le (reverse_core l r) (length l - 1 - i) h1 = nth_le l i h2
| []       r i     h1 h2 := absurd h2 (not_lt_zero _)
| (a :: l) r 0     h1 h2 := begin
    note aux := nth_le_reverse_aux1 l (a :: r) 0,
    rw zero_add at aux,
    exact aux _ (zero_lt_succ _)
  end
| (a :: l) r (i+1) h1 h2 := begin
    note aux := nth_le_reverse_aux2 l (a :: r) i,
    note heq := calc length (a :: l) - 1 - (i + 1)
          = length l - (1 + i) : by rw add_comm; refl
      ... = length l - 1 - i   : by rw nat.sub_sub,
    rw -heq at aux,
    apply aux
  end

@[simp] lemma nth_le_reverse (l : list α) (i : nat) (h1 h2) :
  nth_le (reverse l) (length l - 1 - i) h1 = nth_le l i h2 :=
nth_le_reverse_aux2 _ _ _ _ _

/- last -/

attribute [simp] last

@[simp] lemma last_cons {a : α} {l : list α} : ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil), last (a :: l) h₁ = last l h₂ :=
by {induction l; intros, contradiction, simph, reflexivity}

@[simp] lemma last_append {a : α} (l : list α) (h : l ++ [a] ≠ []) : last (l ++ [a]) h = a :=
begin
  induction l with hd tl ih; rsimp,
  assert haux : tl ++ [a] ≠ [],
    {apply append_ne_nil_of_ne_nil_right, contradiction},
  simph
end

lemma last_concat {a : α} (l : list α) (h : concat l a ≠ []) : last (concat l a) h = a :=
by simph

/- nth -/

attribute [simp] nth

lemma nth_succ (a : α) (l : list α) (n : nat) : nth (a::l) (nat.succ n) = nth l n :=
rfl

/- mem -/

@[simp] lemma mem_nil_iff (a : α) : a ∈ ([] : list α) ↔ false :=
iff.rfl

@[simp] lemma not_mem_nil (a : α) : a ∉ ([] : list α) :=
iff.mp $ mem_nil_iff a

@[simp] lemma mem_cons_self (a : α) (l : list α) : a ∈ a :: l :=
or.inl rfl

@[simp] lemma mem_cons_iff (a y : α) (l : list α) : a ∈ y :: l ↔ (a = y ∨ a ∈ l) :=
iff.rfl

@[rsimp] lemma mem_cons_eq (a y : α) (l : list α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
rfl

lemma eq_nil_of_forall_not_mem : ∀ {l : list α}, (∀ a, a ∉ l) → l = nil
| []        := assume h, rfl
| (b :: l') := assume h, absurd (mem_cons_self b l') (h b)

lemma mem_cons_of_mem (y : α) {a : α} {l : list α} : a ∈ l → a ∈ y :: l :=
assume H, or.inr H

lemma eq_or_mem_of_mem_cons {a y : α} {l : list α} : a ∈ y::l → a = y ∨ a ∈ l :=
assume h, h

lemma mem_singleton {a b : α} : a ∈ [b] → a = b :=
suppose a ∈ [b], or.elim (eq_or_mem_of_mem_cons this)
  (suppose a = b, this)
  (suppose a ∈ [], absurd this (not_mem_nil a))

@[simp] lemma mem_singleton_iff (a b : α) : a ∈ [b] ↔ a = b :=
iff.intro mem_singleton (begin intro h, simp [h] end)

lemma mem_of_mem_cons_of_mem {a b : α} {l : list α} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, or.elim (eq_or_mem_of_mem_cons ainbl)
  (suppose a = b, begin subst a, exact binl end)
  (suppose a ∈ l, this)

lemma mem_or_mem_of_mem_append {a : α} : ∀ {s t : list α}, a ∈ s ++ t → a ∈ s ∨ a ∈ t
| []     t h := or.inr h
| (b::s) t h :=
  have a = b ∨ a ∈ s ++ t, from h,
  match this with
  | or.inl h₁ := or.inl (h₁ ▸ mem_cons_self _ _)
  | or.inr h₁ :=
    have a ∈ s ∨ a ∈ t, from mem_or_mem_of_mem_append h₁,
    match this with
    | or.inl h₂ := or.inl (mem_cons_of_mem _ h₂)
    | or.inr h₂ := or.inr h₂
    end
  end

lemma mem_append_of_mem_or_mem {a : α} {s t : list α} : a ∈ s ∨ a ∈ t → a ∈ s ++ t :=
list.rec_on s
  (take h, or.elim h false.elim id)
  (take b s,
    assume ih : a ∈ s ∨ a ∈ t → a ∈ s ++ t,
    suppose a ∈ b::s ∨ a ∈ t,
      or.elim this
        (suppose a ∈ b::s,
          or.elim (eq_or_mem_of_mem_cons this)
            (suppose a = b, or.inl this)
            (suppose a ∈ s, or.inr (ih (or.inl this))))
        (suppose a ∈ t, or.inr (ih (or.inr this))))

@[simp] lemma mem_append_iff (a : α) (s t : list α) : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t :=
iff.intro mem_or_mem_of_mem_append mem_append_of_mem_or_mem

@[rsimp] lemma mem_append_eq (a : α) (s t : list α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
propext $ mem_append_iff a s t

lemma not_mem_of_not_mem_append_left {a : α} {s t : list α} : a ∉ s++t → a ∉ s :=
λ nainst ains, absurd (mem_append_of_mem_or_mem (or.inl ains)) nainst

lemma not_mem_of_not_mem_append_right {a : α} {s t : list α} : a ∉ s++t → a ∉ t :=
λ nainst aint, absurd (mem_append_of_mem_or_mem (or.inr aint)) nainst

lemma not_mem_append {a : α} {s t : list α} : a ∉ s → a ∉ t → a ∉ s++t :=
λ nains naint ainst, or.elim (mem_or_mem_of_mem_append ainst)
  (λ ains, by contradiction)
  (λ aint, by contradiction)

lemma length_pos_of_mem {a : α} : ∀ {l : list α}, a ∈ l → 0 < length l
| []     := suppose a ∈ [], begin simp at this, contradiction end
| (b::l) := suppose a ∈ b::l, nat.zero_lt_succ _

lemma mem_split {a : α} {l : list α} : a ∈ l → ∃ s t : list α, l = s ++ (a::t) :=
list.rec_on l
  (suppose a ∈ [], begin simp at this, contradiction end)
  (take b l,
    assume ih : a ∈ l → ∃ s t : list α, l = s ++ (a::t),
    suppose a ∈ b::l,
    or.elim (eq_or_mem_of_mem_cons this)
      (suppose a = b, ⟨[], l, begin rw this, reflexivity end⟩)
      (suppose a ∈ l,
        match (ih this) with
        | ⟨s, t, (h : l = s ++ (a::t))⟩ := ⟨b::s, t, begin rw h, reflexivity end⟩
        end))

lemma mem_append_left {a : α} {l₁ : list α} (l₂ : list α) : a ∈ l₁ → a ∈ l₁ ++ l₂ :=
assume ainl₁, mem_append_of_mem_or_mem (or.inl ainl₁)

lemma mem_append_right {a : α} (l₁ : list α) {l₂ : list α} : a ∈ l₂ → a ∈ l₁ ++ l₂ :=
assume ainl₂, mem_append_of_mem_or_mem (or.inr ainl₂)

lemma mem_of_ne_of_mem {a y : α} {l : list α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
or.elim (eq_or_mem_of_mem_cons h₂) (λe, absurd e h₁) (λr, r)

lemma ne_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ≠ b :=
assume nin aeqb, absurd (or.inl aeqb) nin

lemma not_mem_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ∉ l :=
assume nin nainl, absurd (or.inr nainl) nin

lemma not_mem_cons_of_ne_of_not_mem {a y : α} {l : list α} : a ≠ y → a ∉ l → a ∉ y::l :=
assume p1 p2, not.intro (assume Pain, absurd (eq_or_mem_of_mem_cons Pain) (not_or p1 p2))

lemma ne_and_not_mem_of_not_mem_cons {a y : α} {l : list α} : a ∉ y::l → a ≠ y ∧ a ∉ l :=
assume p, and.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)

@[simp] lemma mem_reverse (a : α) (l : list α) : a ∈ reverse l ↔ a ∈ l :=
by induction l; simph; rw mem_append_eq

@[simp] lemma bex_nil_iff_false (p : α → Prop) : (∃ x ∈ @nil α, p x) ↔ false :=
iff_false_intro $ λ⟨x, hx, px⟩, hx

@[simp] lemma ball_nil_iff_true (p : α → Prop) : (∀ x ∈ @nil α, p x) ↔ true :=
iff_true_intro $ λx, false.elim

@[simp] lemma bex_cons (p : α → Prop) (a : α) (l : list α) : (∃ x ∈ (a :: l), p x) ↔ (p a ∨ ∃ x ∈ l, p x) :=
⟨λ⟨x, h, px⟩, by {
  simp at h, cases h with h h, {cases h, exact or.inl px}, {exact or.inr ⟨x, h, px⟩}},
λo, o.elim (λpa, ⟨a, mem_cons_self _ _, pa⟩)
  (λ⟨x, h, px⟩, ⟨x, mem_cons_of_mem _ h, px⟩)⟩

@[simp] lemma ball_cons (p : α → Prop) (a : α) (l : list α) : (∀ x ∈ (a :: l), p x) ↔ (p a ∧ ∀ x ∈ l, p x) :=
⟨λal, ⟨al a (mem_cons_self _ _), λx h, al x (mem_cons_of_mem _ h)⟩,
 λ⟨pa, al⟩ x o, o.elim (λe, e.symm ▸ pa) (al x)⟩

/- list subset -/

protected def subset (l₁ l₂ : list α) := ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance has_subset : has_subset (list α) := ⟨list.subset⟩

@[simp] lemma nil_subset (l : list α) : [] ⊆ l :=
λ b i, false.elim (iff.mp (mem_nil_iff b) i)

@[simp] lemma subset.refl (l : list α) : l ⊆ l :=
λ b i, i

lemma subset.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
λ b i, h₂ (h₁ i)

@[simp] lemma subset_cons (a : α) (l : list α) : l ⊆ a::l :=
λ b i, or.inr i

lemma subset_of_cons_subset {a : α} {l₁ l₂ : list α} : a::l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
λ s b i, s (mem_cons_of_mem _ i)

lemma cons_subset_cons  {l₁ l₂ : list α} (a : α) (s : l₁ ⊆ l₂) : (a::l₁) ⊆ (a::l₂) :=
λ b hin, or.elim (eq_or_mem_of_mem_cons hin)
  (λ e : b = a,  or.inl e)
  (λ i : b ∈ l₁, or.inr (s i))

@[simp] lemma subset_append_left (l₁ l₂ : list α) : l₁ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (or.inl i)

@[simp] lemma subset_append_right (l₁ l₂ : list α) : l₂ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (or.inr i)

lemma subset_cons_of_subset (a : α) {l₁ l₂ : list α} : l₁ ⊆ l₂ → l₁ ⊆ (a::l₂) :=
λ (s : l₁ ⊆ l₂) (a : α) (i : a ∈ l₁), or.inr (s i)

lemma subset_app_of_subset_left (l l₁ l₂ : list α) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₁) (a : α) (ainl : a ∈ l),
  have a ∈ l₁, from s ainl,
  mem_append_of_mem_or_mem (or.inl this)

lemma subset_app_of_subset_right (l l₁ l₂ : list α) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₂) (a : α) (ainl : a ∈ l),
  have a ∈ l₂, from s ainl,
  mem_append_of_mem_or_mem (or.inr this)

lemma cons_subset_of_subset_of_mem {a : α} {l m : list α} (ainm : a ∈ m) (lsubm : l ⊆ m) :
  a::l ⊆ m :=
take b, suppose b ∈ a::l,
or.elim (eq_or_mem_of_mem_cons this)
  (suppose b = a, begin subst b, exact ainm end)
  (suppose b ∈ l, lsubm this)

lemma app_subset_of_subset_of_subset {l₁ l₂ l : list α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
take a, suppose a ∈ l₁ ++ l₂,
or.elim (mem_or_mem_of_mem_append this)
  (suppose a ∈ l₁, l₁subl this)
  (suppose a ∈ l₂, l₂subl this)

/- sublists -/

inductive sublist : list α → list α → Prop
| slnil : sublist [] []
| cons (l₁ l₂ a) : sublist l₁ l₂ → sublist l₁ (a::l₂)
| cons2 (l₁ l₂ a) : sublist l₁ l₂ → sublist (a::l₁) (a::l₂)

infix `<+`:50 := sublist

@[simp] lemma nil_sublist : Π (l : list α), [] <+ l
| []       := sublist.slnil
| (a :: l) := sublist.cons _ _ a (nil_sublist l)

@[simp] lemma sublist.refl : Π (l : list α), l <+ l
| []       := sublist.slnil
| (a :: l) := sublist.cons2 _ _ a (sublist.refl l)

lemma sublist.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ :=
sublist.rec_on h₂ (λ_ s, s)
  (λl₂ l₃ a h₂ IH l₁ h₁, sublist.cons _ _ _ (IH l₁ h₁))
  (λl₂ l₃ a h₂ IH l₁ h₁, @sublist.cases_on _ (λl₁ l₂', l₂' = a :: l₂ → l₁ <+ a :: l₃) _ _ h₁
    (λ_, nil_sublist _)
    (λl₁ l₂' a' h₁' e, match a', l₂', e, h₁' with ._, ._, rfl, h₁ := sublist.cons _ _ _ (IH _ h₁) end)
    (λl₁ l₂' a' h₁' e, match a', l₂', e, h₁' with ._, ._, rfl, h₁ := sublist.cons2 _ _ _ (IH _ h₁) end) rfl)
  l₁ h₁

@[simp] lemma sublist_cons (a : α) (l : list α) : l <+ a::l :=
sublist.cons _ _ _ (sublist.refl l)

lemma sublist_of_cons_sublist {a : α} {l₁ l₂ : list α} : a::l₁ <+ l₂ → l₁ <+ l₂ :=
sublist.trans (sublist_cons a l₁)

lemma cons_sublist_cons  {l₁ l₂ : list α} (a : α) (s : l₁ <+ l₂) : (a::l₁) <+ (a::l₂) :=
sublist.cons2 _ _ _ s

@[simp] lemma sublist_append_left : Π (l₁ l₂ : list α), l₁ <+ l₁++l₂
| []      l₂ := nil_sublist _
| (a::l₁) l₂ := cons_sublist_cons _ (sublist_append_left l₁ l₂)

@[simp] lemma sublist_append_right : Π (l₁ l₂ : list α), l₂ <+ l₁++l₂
| []      l₂ := sublist.refl _
| (a::l₁) l₂ := sublist.cons _ _ _ (sublist_append_right l₁ l₂)

lemma sublist_cons_of_sublist (a : α) {l₁ l₂ : list α} : l₁ <+ l₂ → l₁ <+ (a::l₂) :=
sublist.cons _ _ _

lemma sublist_app_of_sublist_left (l l₁ l₂ : list α) (s : l <+ l₁) : l <+ l₁++l₂ :=
sublist.trans s (sublist_append_left _ _)

lemma sublist_app_of_sublist_right (l l₁ l₂ : list α) (s : l <+ l₂) : l <+ l₁++l₂ :=
sublist.trans s (sublist_append_right _ _)

lemma subset_of_sublist : Π {l₁ l₂ : list α} (s : l₁ <+ l₂) ⦃b⦄ (h : b ∈ l₁), b ∈ l₂
| ._ ._ sublist.slnil b h := h
| ._ ._ (sublist.cons l₁ l₂ a s) b h := mem_cons_of_mem _ (subset_of_sublist s h)
| ._ ._ (sublist.cons2 l₁ l₂ a s) b h :=
  match eq_or_mem_of_mem_cons h with
  | or.inl h := by rw h; exact mem_cons_self _ _
  | or.inr h := mem_cons_of_mem _ (subset_of_sublist s h)
  end

lemma eq_nil_of_map_eq_nil {f : α → β} {l :list α} (h : map f l = nil) : l = nil :=
eq_nil_of_length_eq_zero (begin rw -(length_map f l), simp [h] end)

lemma mem_map (f : α → β) {a : α} {l : list α} (h : a ∈ l) : f a ∈ map f l :=
begin
  induction l with b l' ih,
  {simp at h, contradiction },
  {simp, simp at h, cases h with h h,
    {simph},
    {exact or.inr (ih h)}}
end

lemma exists_of_mem_map {f : α → β} {b : β} {l : list α} (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b :=
begin
  induction l with c l' ih,
  {simp at h, contradiction},
  {cases (eq_or_mem_of_mem_cons h) with h h,
    {existsi c, simp [h]},
    {cases ih h with a ha, cases ha with ha₁ ha₂,
      existsi a, simph }}
end

lemma eq_of_map_const {b₁ b₂ : β} : ∀ {l : list α}, b₁ ∈ map (function.const α b₂) l → b₁ = b₂
| []     h := absurd h (not_mem_nil b₁)
| (a::l) h :=
  or.elim (eq_or_mem_of_mem_cons h)
    (suppose b₁ = b₂, this)
    (suppose b₁ ∈ map (function.const α b₂) l, eq_of_map_const this)

end list
