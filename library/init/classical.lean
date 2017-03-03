/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import init.data.subtype.basic init.funext
open subtype

namespace classical
universes u v

/- the axiom -/
axiom choice {α : Sort u} : nonempty α → α

noncomputable theorem indefinite_description {α : Sort u} (p : α → Prop) :
  (∃ x, p x) → {x // p x} :=
λ h, choice (let ⟨x, px⟩ := h in ⟨⟨x, px⟩⟩)

/- Diaconescu's theorem: using function extensionality and propositional extensionality,
   we can get excluded middle from this. -/
section diaconescu
parameter  p : Prop

private def U (x : Prop) : Prop := x = true ∨ p
private def V (x : Prop) : Prop := x = false ∨ p

private lemma exU : ∃ x, U x := ⟨true, or.inl rfl⟩
private lemma exV : ∃ x, V x := ⟨false, or.inl rfl⟩

private noncomputable def u := elt_of (indefinite_description U exU)
private noncomputable def v := elt_of (indefinite_description V exV)

private lemma u_def : U u := has_property (indefinite_description U exU)
private lemma v_def : V v := has_property (indefinite_description V exV)

private lemma not_uv_or_p : ¬(u = v) ∨ p :=
or.elim u_def
  (assume hut : u = true,
    or.elim v_def
      (assume hvf : v = false,
        have hne : ¬(u = v), from eq.symm hvf ▸ eq.symm hut ▸ true_ne_false,
        or.inl hne)
      (assume hp : p, or.inr hp))
  (assume hp : p, or.inr hp)

private lemma p_implies_uv : p → u = v :=
assume hp : p,
have hpred : U = V, from
  funext (take x : Prop,
    have hl : (x = true ∨ p) → (x = false ∨ p), from
      assume a, or.inr hp,
    have hr : (x = false ∨ p) → (x = true ∨ p), from
      assume a, or.inr hp,
    show (x = true ∨ p) = (x = false ∨ p), from
      propext (iff.intro hl hr)),
have h₀ : ∀ exU exV,
    elt_of (indefinite_description U exU) = elt_of (indefinite_description V exV),
  from hpred ▸ λ exU exV, rfl,
show u = v, from h₀ _ _

theorem em : p ∨ ¬p :=
have h : ¬(u = v) → ¬p, from mt p_implies_uv,
  or.elim not_uv_or_p
    (assume hne : ¬(u = v), or.inr (h hne))
    (assume hp : p, or.inl hp)
end diaconescu

theorem exists_true_of_nonempty {a : Sort u} (h : nonempty a) : ∃ x : a, true :=
nonempty.elim h (take x, ⟨x, trivial⟩)

noncomputable def inhabited_of_nonempty {a : Sort u} (h : nonempty a) : inhabited a :=
⟨elt_of (indefinite_description _ (exists_true_of_nonempty h))⟩

noncomputable def inhabited_of_exists {a : Sort u} {p : a → Prop} (h : ∃ x, p x) :
  inhabited a :=
inhabited_of_nonempty (exists.elim h (λ w hw, ⟨w⟩))

/- all propositions are decidable -/
noncomputable def decidable_inhabited (a : Prop) : inhabited (decidable a) :=
inhabited_of_nonempty
  (or.elim (em a)
    (assume ha, ⟨is_true ha⟩)
    (assume hna, ⟨is_false hna⟩))
local attribute [instance] decidable_inhabited

noncomputable def prop_decidable (a : Prop) : decidable a :=
arbitrary (decidable a)
local attribute [instance] prop_decidable

noncomputable def type_decidable_eq (a : Sort u) : decidable_eq a :=
λ x y, prop_decidable (x = y)

noncomputable def type_decidable (a : Sort u) : psum a (a → false) :=
match (prop_decidable (nonempty a)) with
| (is_true hp)  := psum.inl (@inhabited.default _ (inhabited_of_nonempty hp))
| (is_false hn) := psum.inr (λ a, absurd (nonempty.intro a) hn)
end

noncomputable theorem strong_indefinite_description {a : Sort u} (p : a → Prop)
  (h : nonempty a) : { x : a // (∃ y : a, p y) → p x} :=
match (prop_decidable (∃ x : a, p x)) with
| (is_true hp)  := let xp := indefinite_description _ hp in
                   tag (elt_of xp) (λ h', has_property xp)
| (is_false hn) := tag (@inhabited.default _ (inhabited_of_nonempty h)) (λ h, absurd h hn)
end

/- the Hilbert epsilon function -/

noncomputable def epsilon {a : Sort u} [h : nonempty a] (p : a → Prop) : a :=
elt_of (strong_indefinite_description p h)

theorem epsilon_spec_aux {a : Sort u} (h : nonempty a) (p : a → Prop) (hex : ∃ y, p y) :
    p (@epsilon a h p) :=
have aux : (∃ y, p y) → p (elt_of (strong_indefinite_description p h)), from has_property (strong_indefinite_description p h),
aux hex

theorem epsilon_spec {a : Sort u} {p : a → Prop} (hex : ∃ y, p y) :
    p (@epsilon a (nonempty_of_exists hex) p) :=
epsilon_spec_aux (nonempty_of_exists hex) p hex

theorem epsilon_singleton {a : Sort u} (x : a) : @epsilon a ⟨x⟩ (λ y, y = x) = x :=
@epsilon_spec a (λ y, y = x) ⟨x, rfl⟩

noncomputable def some {a : Sort u} {p : a → Prop} (h : ∃ x, p x) : a :=
@epsilon a (nonempty_of_exists h) p

theorem some_spec {a : Sort u} {p : a → Prop} (h : ∃ x, p x) : p (some h) :=
epsilon_spec h

/- the axiom of choice -/

theorem axiom_of_choice {a : Sort u} {b : a → Sort v} {r : Π x, b x → Prop} (h : ∀ x, ∃ y, r x y) :
  ∃ (f : Π x, b x), ∀ x, r x (f x) :=
have h : ∀ x, r x (some (h x)), from take x, some_spec (h x),
⟨_, h⟩

theorem skolem {a : Sort u} {b : a → Sort v} {p : Π x, b x → Prop} :
  (∀ x, ∃ y, p x y) ↔ ∃ (f : Π x, b x) , (∀ x, p x (f x)) :=
iff.intro
  (assume h : (∀ x, ∃ y, p x y), axiom_of_choice h)
  (assume h : (∃ (f : Π x, b x), (∀ x, p x (f x))),
    take x, exists.elim h (λ (fw : ∀ x, b x) (hw : ∀ x, p x (fw x)),
      ⟨fw x, hw x⟩))

theorem prop_complete (a : Prop) : a = true ∨ a = false :=
or.elim (em a)
  (λ t, or.inl (propext (iff.intro (λ h, trivial) (λ h, t))))
  (λ f, or.inr (propext (iff.intro (λ h, absurd h f) (λ h, false.elim h))))

def eq_true_or_eq_false := prop_complete

section aux
attribute [elab_as_eliminator]
theorem cases_true_false (p : Prop → Prop) (h1 : p true) (h2 : p false) (a : Prop) : p a :=
or.elim (prop_complete a)
  (assume ht : a = true,  eq.symm ht ▸ h1)
  (assume hf : a = false, eq.symm hf ▸ h2)

theorem cases_on (a : Prop) {p : Prop → Prop} (h1 : p true) (h2 : p false) : p a :=
cases_true_false p h1 h2 a

-- this supercedes by_cases in decidable
def by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
or.elim (em p) (assume hp, hpq hp) (assume hnp, hnpq hnp)

-- this supercedes by_contradiction in decidable
theorem by_contradiction {p : Prop} (h : ¬p → false) : p :=
by_cases
  (assume h1 : p, h1)
  (assume h1 : ¬p, false.rec _ (h h1))

theorem eq_false_or_eq_true (a : Prop) : a = false ∨ a = true :=
cases_true_false (λ x, x = false ∨ x = true)
  (or.inr rfl)
  (or.inl rfl)
  a

theorem iff.to_eq {a b : Prop} (h : a ↔ b) : a = b :=
iff.elim (assume h1 h2, propext (iff.intro h1 h2)) h

theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) :=
propext (iff.intro
  (assume h, iff.to_eq h)
  (assume h, h^.to_iff))

lemma eq_false {a : Prop} : (a = false) = (¬ a) :=
have (a ↔ false) = (¬ a), from propext (iff_false a),
eq.subst (@iff_eq_eq a false) this

lemma eq_true {a : Prop} : (a = true) = a :=
have (a ↔ true) = a, from propext (iff_true a),
eq.subst (@iff_eq_eq a true) this
end aux

end classical
