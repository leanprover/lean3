/-
Copyright (c) 2016 Marcos Mazari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Ideals and quotient rings.

Authors: Marcos Mazari, Jeremy Avigad
-/
import data.set algebra.ring theories.move
open function eq.ops algebra set classical

/- TODO: move -/

abbreviation contrapos := @not_imp_not_of_imp

lemma ne_of_not_mem_of_mem {A : Type} {I J : set A} {y : A} (H1 :  y ∉ I) (H2 : y ∈ J) : I ≠ J :=
by intro H; rewrite H at H1; exact H1 H2

lemma exists_mem_and_not_mem_of_not_subset {A : Type} {I J : set A} (H : ¬ J ⊆ I) :
  ∃ y, y ∈ J ∧ y ∉ I :=
obtain x (Hx : ¬ (x ∈ J → x ∈ I)), from exists_not_of_not_forall H,
exists.intro x (and_not_of_not_implies Hx)

lemma exists_mem_and_not_mem_of_ne_of_subset {A : Type} {I J : set A} (H1 : I ≠ J) (H2 : I ⊆ J) :
  ∃ y, y ∈ J ∧ y ∉ I :=
exists_mem_and_not_mem_of_not_subset (assume H, H1 (eq_of_subset_of_subset H2 H))

/- TODO: move to file for additive subgroups -/

section

variable {A : Type}

structure is_zero_closed [class] [has_zero A] (S : set A) : Prop :=
(zero_mem : zero ∈ S)

proposition zero_mem [has_zero A] {S : set A} [is_zero_closed S] : 0 ∈ S :=
is_zero_closed.zero_mem _ S

structure is_add_closed [class] [has_add A] (S : set A) : Prop :=
(add_mem : ∀₀ a ∈ S, ∀₀ b ∈ S, a + b ∈ S)

proposition add_mem [has_add A] {S : set A} [is_add_closed S] {a : A} (aS : a ∈ S) {b : A}
    (bS : b ∈ S) :
  a + b ∈ S :=
is_add_closed.add_mem _ S aS bS

structure is_neg_closed [class] [has_neg A] (S : set A) : Prop :=
(neg_mem : ∀₀ a ∈ S, -a ∈ S)

proposition neg_mem [has_neg A] {S : set A} [is_neg_closed S] {a : A} (aS : a ∈ S) : -a ∈ S :=
is_neg_closed.neg_mem _ S aS

proposition mem_of_neg_mem [add_group A] {S : set A} [is_neg_closed S] {a : A} (naS : -a ∈ S) :
  a ∈ S :=
by rewrite -neg_neg; exact neg_mem naS

proposition neg_mem_iff [add_group A] {S : set A} [is_neg_closed S] (a : A) : -a ∈ S ↔ a ∈ S :=
iff.intro mem_of_neg_mem neg_mem

proposition sub_mem_swap [add_group A] {S : set A} [is_neg_closed S] {a b : A} (H : b - a ∈ S) :
  a - b ∈ S :=
mem_of_neg_mem (by rewrite neg_sub; assumption)

proposition sub_mem_iff [add_group A] {S : set A} [is_neg_closed S] (a b : A) :
  a - b ∈ S ↔ b - a ∈ S :=
iff.intro sub_mem_swap sub_mem_swap

structure is_add_subgroup [class] [add_group A] (S : set A)
  extends is_zero_closed S, is_add_closed S, is_neg_closed S : Prop

definition set_add [has_add A] (S T : set A) : set A := {x | ∃₀ y ∈ S, ∃₀ z ∈ T, x = y + z}

end

namespace set_add
  infix + := set_add
end set_add
open set_add

section

variables {A : Type}

proposition mem_set_add [has_add A] {S T : set A} {a b c : A}
    (aS : a ∈ S) (bT : b ∈ T) (ceq : c = a + b) :
  c ∈ S + T :=
exists.intro a (and.intro aS (exists.intro b (and.intro bT ceq)))

proposition subset_set_add_right [add_monoid A] (S T : set A) [is_zero_closed T] : S ⊆ S + T :=
take a, assume aS, mem_set_add aS zero_mem (by simp)

proposition subset_set_add_left [add_monoid A] (S T : set A) [is_zero_closed S] : T ⊆ S + T :=
take a, assume aT, mem_set_add zero_mem aT (by simp)

end

section
variable {A : Type}
variable [comm_ring A]

structure is_ideal [class] (I : set A) extends is_zero_closed I, is_add_closed I : Prop :=
(mul_arb_mem : ∀ x, ∀₀ y ∈ I, x * y ∈ I)

proposition mul_arb_mem {I : set A} [is_ideal I] (x : A) {y : A} (yI : y ∈ I) : x * y ∈ I :=
is_ideal.mul_arb_mem _ I x yI

proposition is_add_subgroup_of_is_ideal [instance] (I : set A) [is_ideal I] : is_add_subgroup I :=
is_add_subgroup.mk zero_mem (@add_mem _ _ _ _)
  (λ a aI, by rewrite [neg_eq_neg_one_mul]; apply mul_arb_mem _ aI)

proposition mul_arb_mem' {I : set A} [H : is_ideal I] {x : A} (xI : x ∈ I) (y : A) : x * y ∈ I :=
by rewrite mul.comm; apply mul_arb_mem y xI

lemma eq_univ_of_one_mem_of_is_ideal {I : set A} (H : 1 ∈ I) [is_ideal I] : I = univ :=
eq_univ_of_forall (take x, have x * 1 ∈ I, from mul_arb_mem x H, by simp)

theorem is_ideal_inter ( I J : set A) (HI : is_ideal I)
  (HJ : is_ideal J) :  is_ideal (I ∩ J) :=
have H1 : 0 ∈ I ∩ J, from and.intro zero_mem zero_mem,
have H2 : ∀₀ x ∈ I ∩ J, ∀₀ y ∈ I ∩ J, x + y ∈ I ∩ J, from
  take x, assume xIJ, take y, assume yIJ,
  obtain xI xJ, from xIJ,
  obtain yI yJ, from yIJ,
  show x + y ∈ I ∩ J, from and.intro (add_mem xI yI) (add_mem xJ yJ),
have H3 : ∀ x, ∀₀ y ∈ I ∩ J, x * y ∈ I ∩ J, from
  take x y, assume yIJ,
  obtain yI yJ, from yIJ,
  show x * y ∈ I ∩ J, from and.intro (mul_arb_mem x yI)(mul_arb_mem x yJ),
show is_ideal (I ∩ J), from is_ideal.mk H1 H2 H3

theorem is_ideal_singleton_zero : is_ideal '{(0 : A)} :=
have H1 : 0 ∈ '{0}, from mem_singleton 0,
have H2 : ∀₀ x ∈ '{0}, ∀₀ y ∈ '{0}, x + y ∈ '{0}, from
  take x, assume xmem, take y, assume ymem,
  by rewrite [eq_of_mem_singleton xmem, eq_of_mem_singleton ymem, zero_add]; apply mem_singleton,
have H3 : ∀x, ∀₀ y ∈ '{0}, x * y ∈ '{0}, from
  take x y, assume ymem,
  by rewrite [eq_of_mem_singleton ymem, mul_zero]; apply mem_singleton,
is_ideal.mk H1 H2 H3

lemma is_ideal_univ : is_ideal (@univ A) :=
have H1 : 0 ∈ @univ A, from trivial,
have H2:  ∀₀ x ∈ univ, ∀₀ y ∈ univ, x + y ∈ (@univ A), from λ x xmem y ymem, trivial,
have H3 : ∀ x, ∀₀ y ∈ univ, x * y ∈ (@univ A), from λ x y ymem, trivial,
is_ideal.mk H1 H2 H3

lemma is_ideal_set_add [instance] (I J : set A) [is_ideal I] [is_ideal J] : is_ideal (I + J) :=
have H1 : 0 ∈ I + J, from
  mem_set_add zero_mem zero_mem (by simp),
have H2 : ∀₀ x ∈ I + J, ∀₀ y ∈ I + J, x + y ∈ I + J, from
  λ x xmem y ymem,
    obtain ix [ixI [jx [jxJ xeq]]], from xmem,
    obtain iy [iyI [jy [jyJ yeq]]], from ymem,
    show x + y ∈ I + J, from
      mem_set_add (add_mem ixI iyI) (add_mem jxJ jyJ)
        (by rewrite [xeq, yeq, *add.assoc, add.left_comm jx]),
have H3 : ∀ x, ∀₀ y ∈ I + J, x * y ∈ I + J, from
  λ x y ymem,
    obtain iy [iyI [jy [jyJ yeq]]], from ymem,
    show x * y ∈ I + J, from
      mem_set_add (mul_arb_mem x iyI) (mul_arb_mem x jyJ)
        (by rewrite [yeq, left_distrib]),
is_ideal.mk H1 H2 H3

lemma set_add_subset_of_is_ideal {S T I : set A} [is_ideal I] (SsubI : S ⊆ I) (TsubI : T ⊆ I) :
  S + T ⊆ I :=
take x, suppose x ∈ S + T,
obtain s [sS [t [tT xeq]]], from this,
have s + t ∈ I, from add_mem (SsubI sS) (TsubI tT),
show x ∈ I, by rewrite xeq; apply this

/- ideal generated by a set -/

inductive ideal_generated_by (S : set A) : A → Prop :=
| generators_mem : ∀ {x}, x ∈ S → ideal_generated_by S x
| zero_closed    : ideal_generated_by S 0
| add_closed     : ∀ {x y}, ideal_generated_by S x → ideal_generated_by S y →
                     ideal_generated_by S (x + y)
| mul_arb_closed : ∀ r {x}, ideal_generated_by S x → ideal_generated_by S (r * x)

theorem subset_ideal_generated_by (S : set A) : S ⊆ ideal_generated_by S :=
λ x xS, ideal_generated_by.generators_mem xS

theorem is_ideal_ideal_generated_by [instance] (S : set A) : is_ideal (ideal_generated_by S) :=
is_ideal.mk
  (ideal_generated_by.zero_closed S)
  (λ x xmem y ymem, ideal_generated_by.add_closed xmem ymem)
  (λ r x xmem, ideal_generated_by.mul_arb_closed r xmem)

theorem ideal_generated_by_subset {S : set A} {I : set A} [is_ideal I] (H : S ⊆ I) :
  ideal_generated_by S ⊆ I :=
begin
  intro x xiS,
  induction xiS with a ains a b aiS biS aI bI r a aiS aI,
    {exact H ains},
    {exact zero_mem},
    {exact add_mem aI bI},
  exact mul_arb_mem r aI
end

theorem ideal_generated_by_eq {S : set A} {I : set A} [is_ideal I] (SsubI : S ⊆ I)
    (H : ∀ J, is_ideal J → S ⊆ J → I ⊆ J) :
  ideal_generated_by S = I :=
eq_of_subset_of_subset
  (ideal_generated_by_subset SsubI)
  (H _ _ (subset_ideal_generated_by S))

theorem ideal_generated_by_eq_of_is_ideal {S : set A} [is_ideal S] : ideal_generated_by S = S :=
ideal_generated_by_eq (subset.refl _) (λ J iJ sJ, sJ)

definition principal_ideal (a : A) : set A := ideal_generated_by '{a}

theorem mem_principal_ideal (a : A) : a ∈ principal_ideal a :=
subset_ideal_generated_by _ (mem_singleton a)

theorem is_ideal_principal_ideal [instance] (a : A) : is_ideal (principal_ideal a) :=
is_ideal_ideal_generated_by _

theorem principal_ideal_eq (a : A) : principal_ideal a = {b | ∃ r, b = r * a} :=
have is_ideal {b | ∃ r, b = r * a}, from
  is_ideal.mk
    (exists.intro 0 (by simp))
    (λ x xmem y ymem,
      obtain r xeq, from xmem, obtain s yeq, from ymem,
      exists.intro (r + s) (by rewrite [xeq, yeq, right_distrib]))
    (λ x y ymem,
      obtain r yeq, from ymem,
      exists.intro (x * r) (by rewrite [yeq, mul.assoc])),
ideal_generated_by_eq
  (singleton_subset_of_mem (exists.intro 1 (by simp)))
  (take J, suppose is_ideal J, suppose '{a} ⊆ J,
    have a ∈ J, from mem_of_singleton_subset this,
    show {b | ∃ r, b = r * a} ⊆ J, from
      take b, suppose ∃ r, b = r * a,
      obtain r beq, from this,
      show b ∈ J, by rewrite beq; exact mul_arb_mem r `a ∈ J`)

theorem ideal_generated_by_union_eq (S T: set A) :
  ideal_generated_by (S ∪ T) = ideal_generated_by S + ideal_generated_by T :=
-- TODO: why are these needed?
have is_ideal (ideal_generated_by S + ideal_generated_by T), from is_ideal_set_add _ _,
have is_add_subgroup (ideal_generated_by T), from is_add_subgroup_of_is_ideal _,
have is_zero_closed (ideal_generated_by T), from is_add_subgroup.to_is_zero_closed _,
have is_add_subgroup (ideal_generated_by S), from is_add_subgroup_of_is_ideal _,
have is_zero_closed (ideal_generated_by S), from is_add_subgroup.to_is_zero_closed _,
ideal_generated_by_eq
  (union_subset
    (subset.trans (subset_ideal_generated_by S) (subset_set_add_right _ _))
    (subset.trans (subset_ideal_generated_by T) (subset_set_add_left _ _)))
  (take J, assume idealJ, assume JsubST,
    set_add_subset_of_is_ideal
      (ideal_generated_by_subset (subset.trans (subset_union_left _ _) JsubST))
      (ideal_generated_by_subset (subset.trans (subset_union_right _ _) JsubST)))

lemma ideal_generated_by_union_singleton (I : set A) [is_ideal I] (a : A) :
  ideal_generated_by (I ∪ '{a}) = {b | ∃₀ y ∈ I, ∃ z, b = y + z * a} :=
begin
  rewrite [ideal_generated_by_union_eq, ideal_generated_by_eq_of_is_ideal],
  xrewrite [principal_ideal_eq],
  show I + {b | ∃ r, b = r * a} = {b | ∃ x, x ∈ I ∧ ∃ z, b = x + z * a},
    from set.ext (take y, iff.intro
      (assume ymem,
        obtain x [xI [b [[r beq] xeq]]], from ymem,
        exists.intro x (and.intro xI (exists.intro r (by rewrite [xeq, beq]))))
      (assume ymem,
        obtain x [xI [z beq]], from ymem,
        mem_set_add xI (exists.intro z rfl) beq))
end

theorem exists_mul_eq_one_of_two_ideals (H : ∀ I : set A, is_ideal I → I = univ ∨ I = '{0})
    {x : A} (H1 : x ≠ 0) :
  ∃ y, x * y = 1 :=
or.elim (H (principal_ideal x) _)
  (suppose principal_ideal x = univ,
    have 1 ∈ principal_ideal x, by rewrite this; apply mem_univ,
    have ∃r, 1 = r*x, by rewrite [principal_ideal_eq x at this]; apply this,
    obtain r oneeq, from this,
     exists.intro r (by rewrite [oneeq, mul.comm]))
  (suppose principal_ideal x = '{0},
    have x ∈ '{0}, by rewrite -this; apply mem_principal_ideal x,
    have x = 0, from eq_of_mem_singleton this,
    absurd this H1)

theorem principal_ideal_subset {I : set A} [is_ideal I] {a : A} (aI : a ∈ I) :
  principal_ideal a ⊆ I :=
take x,
suppose x ∈ principal_ideal a,
have ∃ r, x = r * a, by rewrite [principal_ideal_eq at this]; apply this,
obtain r xeq, from this,
show x ∈ I, by rewrite xeq; apply mul_arb_mem r aI

theorem exists_mem_and_ne_zero_of_is_ideal {I : set A} [is_ideal I] (H : I ≠ '{0}) :
  ∃ y, y ∈ I ∧ y ≠ 0 :=
have '{0} ⊆ I, from singleton_subset zero_mem,
have ∃y , (y ∈ I ∧  y ∉ '{0}),
  from exists_mem_and_not_mem_of_ne_of_subset (ne.symm H) this,
obtain y [yI ynmem], from this,
exists.intro y (and.intro yI (assume yeq, ynmem (mem_singleton_of_eq yeq)))

theorem eq_univ_of_is_ideal_of_one_mem {I : set A} [is_ideal I] (H : 1 ∈ I) : I = univ :=
eq_univ_of_forall (take x, by rewrite -mul_one; apply mul_arb_mem _ H)

theorem eq_univ_or_eq_singleton_zero_of_is_ideal (H : ∀ x : A , x ≠ 0 → ∃ y, x * y = 1)
  {I : set A} [is_ideal I] : I = univ ∨ I = '{0} :=
by_cases
  (suppose I = '{0}, or.inr this)
  (suppose I ≠ '{0},
    obtain x [xI xne0], from exists_mem_and_ne_zero_of_is_ideal this,
    obtain y (xyeq : x * y = 1), from H x xne0,
    have 1 ∈ I, by rewrite -xyeq; exact mul_arb_mem' xI _,
    have I = univ, from eq_univ_of_is_ideal_of_one_mem this,
    or.inl this)

-- TODO: move
private definition inhabited_of_has_zero [instance] : inhabited A :=
inhabited.mk 0

noncomputable private definition classical_inv (x : A) : A :=
if H : x = 0 then 0 else epsilon (λ y, x * y = 1)

private theorem mul_classical_inv (H : ∀ x : A , x ≠ 0 → ∃ y, x * y = 1) (x : A) (H' : x ≠ 0) :
  x * (classical_inv x) = 1 :=
by rewrite [↑classical_inv, dif_neg H']; apply epsilon_spec (H x H')

private theorem classical_inv_mul (H : ∀ x : A , x ≠ 0 → ∃ y, x * y = 1) (x : A) (H' : x ≠ 0) :
  (classical_inv x) * x = 1 :=
by rewrite [mul.comm, mul_classical_inv H x H']

private theorem classical_inv_zero : classical_inv (0 : A) = 0 :=
by rewrite [↑classical_inv, dif_pos rfl]

noncomputable definition discrete_field_of_comm_ring (H : ∀ x : A , x ≠ 0 → ∃ y, x * y = 1)
    (H' : 0 ≠ 1) :
  discrete_field A :=
⦃ discrete_field, (_ : comm_ring A),
  inv              := classical_inv,
  zero_ne_one      := H',
  inv_mul_cancel   := classical_inv_mul H,
  mul_inv_cancel   := mul_classical_inv H,
  has_decidable_eq := _,
  inv_zero         := classical_inv_zero
⦄

end


/- quotient ring -/

namespace quotient_ring
variables {A : Type} [comm_ring A] (K : set A) [is_ideal K]

local notation  a `~` b :=  b - a ∈ K

private lemma rel_rfl (a : A) : a ~ a := by rewrite sub_self; apply zero_mem

private lemma rel_symm (a b : A) (H : a ~ b) : b ~ a :=
mem_of_neg_mem (by rewrite neg_sub; apply H)

private lemma rel_trans (a b c : A) (H₁ : a ~ b) (H₂ : b ~ c) : a ~ c :=
have c - a = (c - b) + (b - a), by simp,
show c - a ∈ K, by rewrite this; exact add_mem H₂ H₁

private lemma add_well_defined {a1 a2 b1 b2 : A} (H1 : a1 ~ b1) (H2 : a2 ~ b2) :
  a1 + a2 ~ b1 + b2 :=
have (b1 + b2) - (a1 + a2) = (b1 - a1) + (b2 - a2), by simp,
by rewrite this; apply add_mem H1 H2

private lemma neg_well_defined {a  b : A} (H : a ~ b) : (-a ~ -b) :=
mem_of_neg_mem (by rewrite [neg_neg_sub_neg]; apply H)

private lemma mul_well_defined {a1 a2 b1 b2 : A} (H1 : a1 ~  b1) (H2 : a2 ~  b2) :
  a1 * a2 ~ b1 * b2 :=
have b1 * b2 - a1 * a2 = (b1 - a1) * b2 + a1 * (b2 - a2),
  by rewrite [mul_sub_right_distrib, mul_sub_left_distrib, *sub_eq_add_neg, add.assoc,
              neg_add_cancel_left],
begin
  rewrite this, apply add_mem,
    {exact mul_arb_mem' H1 _},
  exact mul_arb_mem _ H2
end

definition quotient_ring_setoid : setoid A :=
setoid.mk (λ a b, b - a ∈ K) (mk_equivalence _ (rel_rfl K) (rel_symm K) (rel_trans K))

local attribute quotient_ring_setoid [instance]

definition quotient [reducible] : Type := quot (quotient_ring_setoid K)

definition qproj (a : A) : quotient K := @quot.mk A (quotient_ring_setoid K) a

infix ` / `      := λ (A' : Type) [comm_ring A'] K' [is_ideal K'], quotient K'
infix ` '+ `:65  := λ {A' : Type} [comm_ring A'] a K' [is_ideal K'], qproj K' a

variable {K}

theorem qproj_eq_qproj {a b : A} (H : b - a ∈ K) : a '+ K = b '+ K :=
quot.sound H

theorem sub_mem_of_qproj_eq_qproj {a b : A} (H : a '+ K = b '+ K) : b - a ∈ K :=
quot.exact H

theorem qproj_eq_qproj_iff (a b : A) : a '+ K = b '+ K ↔ b - a ∈ K :=
iff.intro sub_mem_of_qproj_eq_qproj qproj_eq_qproj

-- TODO: replace in group.quotient as well
proposition quotient_induction {P : A / K → Prop} (h : ∀ a, P (a '+ K)) : ∀ a, P a :=
take a, quot.induction_on a h

proposition quotient_induction_on {P : A / K → Prop} (a : A / K) (h : ∀ a, P (a '+ K)) : P a :=
quot.induction_on a h

proposition quotient_induction₂ {P : A / K → A / K → Prop}
    (h : ∀ a₁ a₂, P (a₁ '+ K) (a₂ '+ K)) :
  ∀ a₁ a₂, P a₁ a₂ :=
take a₁ a₂, quot.induction_on₂ a₁ a₂ h

proposition quotient_induction_on₂ {P : A / K → A / K → Prop}
    (a₁ a₂ : A / K) (h : ∀ a₁ a₂, P (a₁ '+ K) (a₂ '+ K)) :
  P a₁ a₂ :=
quot.induction_on₂ a₁ a₂ h

proposition exists_eq_qproj : ∀ a : A / K, ∃ a', a = a' '+ K :=
quotient_induction (λ a, exists.intro _ rfl)

private definition qadd : A / K → A / K → A / K :=
quot.lift₂
  (λ a b, (a + b) '+ K)
  (take a₁ a₂ b₁ b₂, assume Ha : a₁ ~ b₁, assume Hb : a₂ ~ b₂,
    quot.sound (add_well_defined K Ha Hb))

private definition qmul : A / K → A / K → A / K :=
quot.lift₂
  (λ a b, (a * b) '+ K)
  (take a₁ a₂ b₁ b₂, assume Ha : a₁ ~ b₁, assume Hb : a₂ ~ b₂,
    quot.sound (mul_well_defined K Ha Hb))

private definition qzero : A / K := 0 '+ K

private definition qone : A / K := 1 '+ K

private lemma qproj_eq_qproj_of_eq {a b : A} (H : a = b) : (a '+ K) = (b '+ K) := by rewrite H

private theorem qadd_comm (a b : A / K) : qadd a b = qadd b a :=
quot.induction_on₂ a b
  (take a b, qproj_eq_qproj_of_eq (add.comm a b))

private theorem qadd_assoc (a b c : A / K) : qadd (qadd a b) c = qadd a (qadd b c) :=
quot.induction_on₃ a b c
  (take a b c, qproj_eq_qproj_of_eq (add.assoc a b c))

private definition qneg : A / K → A / K :=
quot.lift
  (λ a , (-a) '+ K)
  (take a1 a2, assume Ha : a1 ~ a2, quot.sound (neg_well_defined K Ha))

private theorem qadd_left_inverse (a : A/ K) : qadd (qneg a) a = qzero :=
quot.induction_on a
  (take a, qproj_eq_qproj_of_eq (add.left_inv a))

private theorem zero_qadd (a : A / K) : qadd qzero a = a :=
quot.induction_on a
  (take a, qproj_eq_qproj_of_eq (zero_add a))

private theorem qadd_zero (a  : A / K) : qadd a qzero = a  :=
quot.induction_on a
  (take a, qproj_eq_qproj_of_eq (add_zero a))

private theorem qmul_comm (a b : A / K) : qmul a b = qmul b a :=
quot.induction_on₂ a b
  (take a b, qproj_eq_qproj_of_eq (mul.comm a b))

private theorem  qmul_assoc (a b c : A / K) : qmul (qmul a b) c = qmul a (qmul b c) :=
quot.induction_on₃ a b c
  (take a b c, qproj_eq_qproj_of_eq (mul.assoc a b c))

private theorem one_qmul (a  : A / K) : qmul qone a = a  :=
quot.induction_on a
  (take a, qproj_eq_qproj_of_eq (one_mul a))

private theorem qmul_one (a  : A / K) : qmul  a qone = a  :=
quot.induction_on a
  (take a, qproj_eq_qproj_of_eq (mul_one a))

private theorem left_distrib (a b c : A/K) : qmul a (qadd b c)= qadd (qmul a b) (qmul a c) :=
quot.induction_on₃ a b c
  (take a b c, qproj_eq_qproj_of_eq (left_distrib a b c))

private theorem right_distrib (a b c : A/K) : qmul (qadd a b) c = qadd (qmul a c) (qmul b c) :=
quot.induction_on₃ a b c
  (take a b c, qproj_eq_qproj_of_eq (right_distrib a b c))

private theorem qadd_comm (a b : A / K) : qadd a b = qadd b a :=
quot.induction_on b
  (quot.induction_on a
    (take a b,
      have (b + a) - (a + b) = 0, by simp,
      have (b + a) - (a + b) ∈ K, by rewrite this; exact zero_mem,
      quot.sound this))

protected definition to_ring [instance] : comm_ring (quotient K) :=
⦃ comm_ring,
  add           := qadd,
  add_assoc     := qadd_assoc,
  zero          := qzero,
  zero_add      := zero_qadd,
  add_zero      := qadd_zero,
  neg           := qneg,
  add_left_inv  := qadd_left_inverse,
  add_comm      := qadd_comm,
  mul           := qmul,
  mul_assoc     := qmul_assoc,
  one           := qone,
  one_mul       := one_qmul,
  mul_one       := qmul_one,
  left_distrib  := left_distrib,
  right_distrib := right_distrib,
  mul_comm      := qmul_comm
⦄

variable (K)
theorem qproj_zero : 0 '+ K = 0 := rfl
theorem qproj_one : 1 '+ K = 1 := rfl
variable {K}

theorem qproj_eq_zero_iff (a : A) : a '+ K = 0 ↔ a ∈ K :=
by krewrite [qproj_eq_qproj_iff, sub_mem_iff, sub_zero]

theorem mem_of_qproj_eq_zero {a : A} (H : a '+ K = 0 '+ K) : a ∈ K :=
iff.mp (qproj_eq_zero_iff a) H

theorem qproj_eq_zero {a : A} (H : a ∈ K) : a '+ K = 0 :=
iff.mpr (qproj_eq_zero_iff a) H

end quotient_ring

/- prime and maximal ideals -/

section
variables {A : Type} [comm_ring A]
open quotient_ring

structure is_prime_ideal [class] (I : set A) extends is_ideal I : Prop :=
(is_prime : ∀ ⦃a b⦄, a * b ∈ I → a ∈ I ∨ b ∈ I)
(nontrivial : I ≠ univ)

structure is_maximal_ideal [class] (I : set A) extends is_ideal I : Prop :=
(is_maximal : ∀ ⦃J : set A⦄, is_ideal J → J ⊇ I → J = I ∨ J = univ)
(nontrivial : I ≠ univ)

theorem mem_or_mem_of_is_prime {I : set A} [is_prime_ideal I] {a b : A} (H : a * b ∈ I) :
  a ∈ I ∨ b ∈ I :=
is_prime_ideal.is_prime H

theorem ne_univ_of_is_prime (I : set A) [is_prime_ideal I] : I ≠ univ :=
@is_prime_ideal.nontrivial _ _ I _

theorem is_maximal {I : set A} [is_maximal_ideal I] {J : set A} [idealJ : is_ideal J] (H : J ⊇ I) :
  J = I ∨ J = univ :=
is_maximal_ideal.is_maximal idealJ H

theorem qproj_eq_zero_or_qproj_eq_zero_of_is_prime_ideal {I : set A} [is_prime_ideal I] (a b : A)
    (H : (a '+ I) * (b '+ I) = 0) :
  a '+ I = 0 ∨ b '+ I = 0 :=
begin
  rewrite [+qproj_eq_zero_iff],
  apply mem_or_mem_of_is_prime,
  apply mem_of_qproj_eq_zero,
  exact H
end

theorem is_prime_ideal_of_forall {I : set A} [is_ideal I]
    (H : ∀ a b, (a '+ I) * (b '+ I) = 0 → a '+ I = 0 ∨ b '+ I = 0) (H' : I ≠ univ) :
  is_prime_ideal I :=
⦃ is_prime_ideal, (_ : is_ideal I),
  is_prime   := begin
                  intro a b abI,
                  rewrite [-+qproj_eq_zero_iff],
                  apply H,
                  exact qproj_eq_zero abI
                end,
  nontrivial := H'
⦄

theorem exists_qproj_mul_qproj_eq_one_of_is_maximal {I : set A} [is_maximal_ideal I] {a : A}
    (H : a '+ I ≠ 0) :
  ∃ y, (a '+ I) * (y '+ I) = 1 :=
have ideal_generated_by (I ∪ '{a}) ≠ I, from
  assume otherwise,
  have a ∈ ideal_generated_by (I ∪ '{a}),
    from subset_ideal_generated_by _ (mem_unionr (mem_singleton _)),
  have a ∉ I, from λ H', H (qproj_eq_zero H'),
  show false, begin apply this, rewrite -otherwise, assumption end,
have ideal_generated_by (I ∪ '{a}) = univ, from
  or.resolve_left
    (is_maximal (subset.trans (subset_union_left _ _) (subset_ideal_generated_by _))) this,
have 1 ∈ {b | ∃₀ y ∈ I, ∃ z, b = y + z * a},
  by rewrite [-ideal_generated_by_union_singleton, this]; apply mem_univ,
obtain y [yI [z (oneeq : 1 = y + z * a)]], from this,
exists.intro z (qproj_eq_qproj
    (show 1 - a * z ∈ I, by rewrite [oneeq, mul.comm, add_sub_cancel]; exact yI))

theorem is_maximal_ideal_of_forall {I : set A} [is_ideal I]
    (H : ∀ a, a '+ I ≠ 0 → ∃ y, (a '+ I)  * (y '+ I) = 1) (H' : I ≠ univ) :
  is_maximal_ideal I :=
⦃ is_maximal_ideal, (_ : is_ideal I),
  is_maximal := take J, suppose is_ideal J, suppose J ⊇ I,
                by_cases
                  (suppose J = I, or.inl this)
                  (suppose J ≠ I,
                    obtain a [aJ anI],
                      from exists_mem_and_not_mem_of_ne_of_subset (ne.symm this) `J ⊇ I`,
                    have a '+ I ≠ 0, from λ H', anI (mem_of_qproj_eq_zero H'),
                    obtain y (Hy : (a '+ I)  * (y '+ I) = 1), from H _ this,
                    have 1 - a * y ∈ I, from sub_mem_of_qproj_eq_qproj Hy,
                    have 1 - a * y + a * y ∈ J, from add_mem (`J ⊇ I` this) (mul_arb_mem' aJ _),
                    have 1 ∈ J, by rewrite [sub_add_cancel at this]; exact this,
                    show J = I ∨ J = univ, from or.inr (eq_univ_of_is_ideal_of_one_mem this)),
  nontrivial := H'
⦄

definition integral_domain_quotient_of_is_prime_ideal [instance] (I : set A) [is_prime_ideal I] :
  integral_domain (A / I) :=
have H : ∀ a b : A / I, a * b = 0 → a = 0 ∨ b = 0, from
  quotient_induction₂ qproj_eq_zero_or_qproj_eq_zero_of_is_prime_ideal,
have H' : (0 : A / I) ≠ 1, from
  assume otherwise,
  have 1 - 0 ∈ I, from sub_mem_of_qproj_eq_qproj otherwise,
  have I = univ, from eq_univ_of_is_ideal_of_one_mem (by rewrite [sub_zero at this]; exact this),
  show false, from is_prime_ideal.nontrivial _ I this,
⦃ integral_domain, (_ : comm_ring (A / I)),
  eq_zero_or_eq_zero_of_mul_eq_zero := H,
  zero_ne_one                       := H'
⦄

theorem is_prime_ideal_of_forall_quotient {I : set A} [is_ideal I]
    (H : ∀ a b : A / I, a * b = 0 → a = 0 ∨ b = 0) (H' : I ≠ univ) :
  is_prime_ideal I :=
is_prime_ideal_of_forall (λ a b, H _ _) H'

noncomputable definition discrete_field_quotient_of_is_maximal_ideal [instance]
    (I : set A) [is_maximal_ideal I] :
  discrete_field (A / I) :=
have H : ∀ x : A / I, x ≠ 0 → ∃ y, x * y = 1, from
  quotient_induction
    (take a, assume anz,
      obtain y Hy, from exists_qproj_mul_qproj_eq_one_of_is_maximal anz,
      exists.intro (y '+ I) Hy),
have H' : (0 : A / I) ≠ 1, from
  assume otherwise,
  have 1 - 0 ∈ I, from sub_mem_of_qproj_eq_qproj otherwise,
  have I = univ, from eq_univ_of_is_ideal_of_one_mem (by rewrite [sub_zero at this]; exact this),
  show false, from is_maximal_ideal.nontrivial _ I this,
discrete_field_of_comm_ring H H'

theorem is_maximal_ideal_of_forall_quotient {I : set A} [is_ideal I]
    (H : ∀ a : A / I, a ≠ 0 → ∃ b, a * b = 1) (H' : I ≠ univ) :
  is_maximal_ideal I :=
is_maximal_ideal_of_forall
  (λ a aIne0,
    obtain b Hb, from H _ aIne0,
    obtain b' (beq : b = b' '+ I), from exists_eq_qproj b,
    exists.intro b' (by rewrite -beq; exact Hb))
  H'

theorem is_prime_ideal_of_is_maximal_ideal [instance] {I : set A} [is_maximal_ideal I] :
  is_prime_ideal I :=
is_prime_ideal_of_forall_quotient
  (@eq_zero_or_eq_zero_of_mul_eq_zero _ _)
  (is_maximal_ideal.nontrivial _ I)

end
