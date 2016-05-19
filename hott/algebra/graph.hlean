/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Graphs and operations on graphs

Currently we only define the notion of a path in a graph, and prove properties and operations on
paths.
-/

open eq sigma nat

/-
  A path is a list of vertexes which are adjacent. We maybe use a weird ordering of cons, because
  the major example where we use this is a category where this ordering makes more sense.
  For the operations on paths we use the names from the corresponding operations on lists. Opening
  both the list and the paths namespace will lead to many name clashes, so that is not advised.
-/

inductive paths {A : Type} (R : A → A → Type) : A → A → Type :=
| nil {} : Π{a : A}, paths R a a
| cons   : Π{a₁ a₂ a₃ : A} (r : R a₂ a₃), paths R a₁ a₂ → paths R a₁ a₃

namespace paths

  notation h :: t  := cons h t
  notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

  variables {A : Type} {R : A → A → Type} {a a' a₁ a₂ a₃ a₄ : A}

  definition concat (r : R a₁ a₂) (l : paths R a₂ a₃) : paths R a₁ a₃ :=
  begin
    induction l with a a₂ a₃ a₄ r' l IH,
    { exact [r]},
    { exact r' :: IH r}
  end

  theorem concat_nil (r : R a₁ a₂) : concat r (@nil A R a₂) = [r] := idp

  theorem concat_cons (r : R a₁ a₂) (r' : R a₃ a₄) (l : paths R a₂ a₃)
    : concat r (r'::l)  = r'::(concat r l) := idp

  definition append (l₂ : paths R a₂ a₃) (l₁ : paths R a₁ a₂) :
    paths R a₁ a₃ :=
  begin
    induction l₂,
    { exact l₁},
    { exact cons r (v_0 l₁)}
  end

  infix ` ++ ` := append

  definition nil_append (l : paths R a₁ a₂) : nil ++ l = l := idp
  definition cons_append (r : R a₃ a₄) (l₂ : paths R a₂ a₃) (l₁ : paths R a₁ a₂) :
    (r :: l₂) ++ l₁ = r :: (l₂ ++ l₁) := idp

  definition singleton_append (r : R a₂ a₃) (l : paths R a₁ a₂) : [r] ++ l = r :: l := idp
  definition append_singleton (l : paths R a₂ a₃) (r : R a₁ a₂) : l ++ [r] = concat r l :=
  begin
    induction l,
    { reflexivity},
    { exact ap (cons r) !v_0}
  end

  definition append_nil (l : paths R a₁ a₂) : l ++ nil = l :=
  begin
    induction l,
    { reflexivity},
    { exact ap (cons r) v_0}
  end

  definition append_assoc (l₃ : paths R a₃ a₄) (l₂ : paths R a₂ a₃)
    (l₁ : paths R a₁ a₂) : (l₃ ++ l₂) ++ l₁ = l₃ ++ (l₂ ++ l₁) :=
  begin
    induction l₃,
    { reflexivity},
    { refine ap (cons r) !v_0}
  end

  theorem append_concat (l₂ : paths R a₃ a₄) (l₁ : paths R a₂ a₃) (r : R a₁ a₂) :
    l₂ ++ concat r l₁ = concat r (l₂ ++ l₁) :=
  begin
    induction l₂,
    { reflexivity},
    { exact ap (cons r_1) !v_0}
  end

  theorem concat_append (l₂ : paths R a₃ a₄) (r : R a₂ a₃) (l₁ : paths R a₁ a₂) :
    concat r l₂ ++ l₁ = l₂ ++ r :: l₁ :=
  begin
    induction l₂,
    { reflexivity},
    { exact ap (cons r) !v_0}
  end

  definition paths.rec_tail {C : Π⦃a a' : A⦄, paths R a a' → Type}
  (H0 : Π {a : A}, @C a a nil)
  (H1 : Π {a₁ a₂ a₃ : A} (r : R a₁ a₂) (l : paths R a₂ a₃), C l → C (concat r l)) :
  Π{a a' : A} (l : paths R a a'), C l :=
  begin
    have Π{a₁ a₂ a₃ : A} (l₂ : paths R a₂ a₃) (l₁ : paths R a₁ a₂) (c : C l₂),
      C (l₂ ++ l₁),
    begin
      intros, revert a₃ l₂ c, induction l₁: intros a₃ l₂ c,
      { rewrite append_nil, exact c},
      { rewrite [-concat_append], apply v_0, apply H1, exact c}
    end,
    intros, rewrite [-nil_append], apply this, apply H0
  end

  definition cons_eq_concat (r : R a₂ a₃) (l : paths R a₁ a₂) :
    Σa (r' : R a₁ a) (l' : paths R a a₃), r :: l = concat r' l' :=
  begin
    revert a₃ r, induction l: intros a₃' r',
    { exact ⟨a₃', r', nil, idp⟩},
    { cases (v_0 a₃ r) with a₄ w, cases w with r₂ w, cases w with l p, clear v_0,
      exact ⟨a₄, r₂, r' :: l, ap (cons r') p⟩}
  end

  definition length (l : paths R a₁ a₂) : ℕ :=
  begin
    induction l,
    { exact 0},
    { exact succ v_0}
  end

  /- If we can reverse edges in the graph we can reverse paths -/

  definition reverse (rev : Π⦃a a'⦄, R a a' → R a' a) (l : paths R a₁ a₂) :
    paths R a₂ a₁ :=
  begin
    induction l,
    { exact nil},
    { exact concat (rev r) v_0}
  end

  theorem reverse_nil (rev : Π⦃a a'⦄, R a a' → R a' a) : reverse rev (@nil A R a₁) = [] := idp

  theorem reverse_cons (rev : Π⦃a a'⦄, R a a' → R a' a) (r : R a₂ a₃) (l : paths R a₁ a₂) :
    reverse rev (r::l) = concat (rev r) (reverse rev l) := idp

  theorem reverse_singleton (rev : Π⦃a a'⦄, R a a' → R a' a) (r : R a₁ a₂) :
    reverse rev [r] = [rev r] := idp

  theorem reverse_pair (rev : Π⦃a a'⦄, R a a' → R a' a) (r₂ : R a₂ a₃) (r₁ : R a₁ a₂) :
    reverse rev [r₂, r₁] = [rev r₁, rev r₂] := idp

  theorem reverse_concat (rev : Π⦃a a'⦄, R a a' → R a' a) (r : R a₁ a₂) (l : paths R a₂ a₃) :
    reverse rev (concat r l) = rev r :: (reverse rev l) :=
  begin
    induction l,
    { reflexivity},
    { rewrite [concat_cons, reverse_cons, v_0]}
  end

  theorem reverse_append (rev : Π⦃a a'⦄, R a a' → R a' a) (l₂ : paths R a₂ a₃)
    (l₁ : paths R a₁ a₂) : reverse rev (l₂ ++ l₁) = reverse rev l₁ ++ reverse rev l₂ :=
  begin
    induction l₂,
    { exact !append_nil⁻¹},
    { rewrite [cons_append, +reverse_cons, append_concat, v_0]}
  end

  definition realize (P : A → A → Type) (f : Π⦃a a'⦄, R a a' → P a a') (ρ : Πa, P a a)
    (c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃)
    ⦃a a' : A⦄ (l : paths R a a') : P a a' :=
  begin
    induction l,
    { exact ρ a},
    { exact c v_0 (f r)}
  end

  definition realize_nil (P : A → A → Type) (f : Π⦃a a'⦄, R a a' → P a a') (ρ : Πa, P a a)
    (c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃) (a : A) :
    realize P f ρ c nil = ρ a :=
  idp

  definition realize_cons (P : A → A → Type) (f : Π⦃a a'⦄, R a a' → P a a') (ρ : Πa, P a a)
    (c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃)
    ⦃a₁ a₂ a₃ : A⦄ (r : R a₂ a₃) (l : paths R a₁ a₂) :
    realize P f ρ c (r :: l) = c (realize P f ρ c l) (f r) :=
  idp

  theorem realize_singleton {P : A → A → Type} {f : Π⦃a a'⦄, R a a' → P a a'} {ρ : Πa, P a a}
    {c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃}
    (id_left : Π⦃a₁ a₂⦄ (p : P a₁ a₂), c (ρ a₁) p = p)
    ⦃a₁ a₂ : A⦄ (r : R a₁ a₂) :
    realize P f ρ c [r] = f r :=
  id_left (f r)

  theorem realize_pair {P : A → A → Type} {f : Π⦃a a'⦄, R a a' → P a a'} {ρ : Πa, P a a}
    {c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃}
    (id_left : Π⦃a₁ a₂⦄ (p : P a₁ a₂), c (ρ a₁) p = p)
    ⦃a₁ a₂ a₃ : A⦄ (r₂ : R a₂ a₃) (r₁ : R a₁ a₂) :
    realize P f ρ c [r₂, r₁] = c (f r₁) (f r₂) :=
  ap (λx, c x (f r₂)) (realize_singleton id_left r₁)

  theorem realize_append {P : A → A → Type} {f : Π⦃a a'⦄, R a a' → P a a'} {ρ : Πa, P a a}
    {c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃}
    (assoc : Π⦃a₁ a₂ a₃ a₄⦄ (p : P a₁ a₂) (q : P a₂ a₃) (r : P a₃ a₄), c (c p q) r = c p (c q r))
    (id_right : Π⦃a₁ a₂⦄ (p : P a₁ a₂), c p (ρ a₂) = p)
    ⦃a₁ a₂ a₃ : A⦄ (l₂ : paths R a₂ a₃) (l₁ : paths R a₁ a₂) :
    realize P f ρ c (l₂ ++ l₁) = c (realize P f ρ c l₁) (realize P f ρ c l₂) :=
  begin
    induction l₂,
    { exact !id_right⁻¹},
    { rewrite [cons_append, +realize_cons, v_0, assoc]}
  end

  /-
    We sometimes want to take quotients of paths (this library was developed to define the pushout of
    categories). The definition paths_rel will - given some basic reduction rules codified by Q -
    extend the reduction to a reflexive transitive relation respecting concatenation of paths.
  -/

  inductive paths_rel {A : Type} {R : A → A → Type}
    (Q : Π⦃a a' : A⦄, paths R a a' → paths R a a' → Type)
    : Π⦃a a' : A⦄, paths R a a' → paths R a a' → Type :=
  | rrefl  : Π{a a' : A} (l : paths R a a'), paths_rel Q l l
  | rel    : Π{a₁ a₂ a₃ : A} {l₂ l₃ : paths R a₂ a₃} (l : paths R a₁ a₂) (q : Q l₂ l₃),
      paths_rel Q (l₂ ++ l) (l₃ ++ l)
  | rcons  : Π{a₁ a₂ a₃ : A} {l₁ l₂ : paths R a₁ a₂} (r : R a₂ a₃),
      paths_rel Q l₁ l₂ → paths_rel Q (cons r l₁) (cons r l₂)
  | rtrans : Π{a₁ a₂ : A} {l₁ l₂ l₃ : paths R a₁ a₂},
      paths_rel Q l₁ l₂ → paths_rel Q l₂ l₃ → paths_rel Q l₁ l₃

  open paths_rel
  attribute rrefl [refl]
  attribute rtrans [trans]
  variables {Q : Π⦃a a' : A⦄, paths R a a' → paths R a a' → Type}

  definition paths_rel_of_Q {l₁ l₂ : paths R a₁ a₂} (q : Q l₁ l₂) :
    paths_rel Q l₁ l₂ :=
  begin
    rewrite [-append_nil l₁, -append_nil l₂], exact rel nil q,
  end

  theorem rel_respect_append_left (l : paths R a₂ a₃) {l₃ l₄ : paths R a₁ a₂}
    (H : paths_rel Q l₃ l₄) : paths_rel Q (l ++ l₃) (l ++ l₄) :=
  begin
    induction l,
    { exact H},
    { exact rcons r (v_0 _ _ H)}
  end

  theorem rel_respect_append_right {l₁ l₂ : paths R a₂ a₃} (l : paths R a₁ a₂)
    (H₁ : paths_rel Q l₁ l₂) : paths_rel Q (l₁ ++ l) (l₂ ++ l) :=
  begin
    induction H₁ with a₁ a₂ l₁
                      a₂ a₃ a₄ l₂ l₂' l₁ q
                      a₂ a₃ a₄ l₁ l₂ r H₁ IH
                      a₂ a₃ l₁ l₂ l₂' H₁ H₁' IH IH',
    { reflexivity},
    { rewrite [+ append_assoc], exact rel _ q},
    { exact rcons r (IH l) },
    { exact rtrans (IH l) (IH' l)}
  end

  theorem rel_respect_append {l₁ l₂ : paths R a₂ a₃} {l₃ l₄ : paths R a₁ a₂}
    (H₁ : paths_rel Q l₁ l₂) (H₂ : paths_rel Q l₃ l₄) :
    paths_rel Q (l₁ ++ l₃) (l₂ ++ l₄) :=
  begin
    induction H₁ with a₁ a₂ l
                      a₂ a₃ a₄ l₂ l₂' l q
                      a₂ a₃ a₄ l₁ l₂ r H₁ IH
                      a₂ a₃ l₁ l₂ l₂' H₁ H₁' IH IH',
    { exact rel_respect_append_left _ H₂},
    { rewrite [+ append_assoc], transitivity _, exact rel _ q,
      apply rel_respect_append_left, apply rel_respect_append_left, exact H₂},
    { exact rcons r (IH _ _ H₂) },
    { refine rtrans (IH _ _ H₂) _, apply rel_respect_append_right, exact H₁'}
  end

  /- assuming some extra properties the relation respects reversing -/

  theorem rel_respect_reverse (rev : Π⦃a a'⦄, R a a' → R a' a) {l₁ l₂ : paths R a₁ a₂}
    (H : paths_rel Q l₁ l₂)
    (rev_rel : Π⦃a a' : A⦄ {l l' : paths R a a'},
      Q l l' → paths_rel Q (reverse rev l) (reverse rev l')) :
    paths_rel Q (reverse rev l₁) (reverse rev l₂) :=
  begin
    induction H,
    { reflexivity},
    { rewrite [+ reverse_append], apply rel_respect_append_left, apply rev_rel q},
    { rewrite [+reverse_cons,-+append_singleton], apply rel_respect_append_right, exact v_0},
    { exact rtrans v_0 v_1}
  end

  theorem rel_left_inv (rev : Π⦃a a'⦄, R a a' → R a' a) (l : paths R a₁ a₂)
    (li : Π⦃a a' : A⦄ (r : R a a'), paths_rel Q [rev r, r] nil) :
    paths_rel Q (reverse rev l ++ l) nil :=
  begin
    induction l,
    { reflexivity},
    { rewrite [reverse_cons, concat_append],
      refine rtrans _ v_0, apply rel_respect_append_left,
      exact rel_respect_append_right _ (li r)}
  end

  theorem rel_right_inv (rev : Π⦃a a'⦄, R a a' → R a' a) (l : paths R a₁ a₂)
    (ri : Π⦃a a' : A⦄ (r : R a a'), paths_rel Q [r, rev r] nil) :
    paths_rel Q (l ++ reverse rev l) nil :=
  begin
    induction l using paths.rec_tail,
    { reflexivity},
    { rewrite [reverse_concat, concat_append],
      refine rtrans _ a, apply rel_respect_append_left,
      exact rel_respect_append_right _ (ri r)}
  end

  definition realize_eq {P : A → A → Type} {f : Π⦃a a'⦄, R a a' → P a a'} {ρ : Πa, P a a}
    {c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃}
    (assoc : Π⦃a₁ a₂ a₃ a₄⦄ (p : P a₁ a₂) (q : P a₂ a₃) (r : P a₃ a₄), c (c p q) r = c p (c q r))
    (id_right : Π⦃a₁ a₂⦄ (p : P a₁ a₂), c p (ρ a₂) = p)
    (resp_rel : Π⦃a₁ a₂⦄ {l₁ l₂ : paths R a₁ a₂}, Q l₁ l₂ →
      realize P f ρ c l₁ = realize P f ρ c l₂)
    ⦃a a' : A⦄ {l l' : paths R a a'} (H : paths_rel Q l l') :
    realize P f ρ c l = realize P f ρ c l' :=
  begin
    induction H,
    { reflexivity},
    { rewrite [+realize_append assoc id_right], apply ap (c _), exact resp_rel q},
    { exact ap (λx, c x (f r)) v_0},
    { exact v_0 ⬝ v_1}
  end


end paths
