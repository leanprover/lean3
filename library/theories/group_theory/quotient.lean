/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Zipperer, Jeremy Avigad

We provide two versions of the quoptient construction. They use the same names and notation:
one lives in the namespace 'quotient_group' and the other lives in the namespace
'quotient_group_general'.

The first takes a group, A, and a normal subgroup, H. We have

  quotient H       := the quotient of A by H
  qproj H a        := the projection, with notation a' * G
  qproj H ' s      := the image of s, with notation s / G
  extend H respf   := given f : A → B respecting the equivalence relation, we get a function
                      f : quotient G → B
  bar f            := the above, G = ker f)

The definition is constructive, using quotient types. We prove all the characteristic properties.

As in the SSReflect library, we also provide a construction to quotient by an *arbitrary subgroup*.
Now we have

  quotient H       := the quotient of normalizer H by H
  qproj H a        := still denoted a '* H, the projection when a is in normalizer H,
                      arbitrary otherwise
  qproj H G        := still denoted G / H, the image of the above
  extend H G respf := given a homomorphism on G with ker_in G f ⊆ H, extends to a
                      homomorphism G / H
  bar G f          := the above, with H = ker_in f G

This quotient H is defined by composing the first one with the construction which turns
normalizer H into a group.
-/
import .subgroup_to_group theories.move
open set function subtype classical quot

namespace group_theory
open coset_notation

variables {A B C : Type}

/- the quotient group -/

namespace quotient_group

variables [group A] (H : set A) [is_normal H]

definition lcoset_setoid [instance] : setoid A :=
setoid.mk (lcoset_equiv H) (equivalence_lcoset_equiv H)

definition quotient := quot (lcoset_setoid H)

private definition qone : quotient H := ⟦ 1 ⟧

private definition qmul : quotient H → quotient H → quotient H :=
quot.lift₂
  (λ a b, ⟦a * b⟧)
  (λ a₁ a₂ b₁ b₂ e₁ e₂, quot.sound (lcoset_equiv_mul H e₁ e₂))

private definition qinv : quotient H → quotient H :=
quot.lift
  (λ a, ⟦a⁻¹⟧)
  (λ a₁ a₂ e, quot.sound (lcoset_equiv_inv H e))

private proposition qmul_assoc (a b c : quotient H) :
  qmul H (qmul H a b) c = qmul H a (qmul H b c) :=
quot.induction_on₂ a b (λ a b, quot.induction_on c (λ c,
  have H :  ⟦a * b * c⟧ = ⟦a * (b * c)⟧, by rewrite mul.assoc,
  H))

private proposition qmul_qone (a : quotient H) : qmul H a (qone H) = a :=
quot.induction_on a (λ a', show ⟦a' * 1⟧ = ⟦a'⟧, by rewrite mul_one)

private proposition qone_qmul (a : quotient H) : qmul H (qone H) a = a :=
quot.induction_on a (λ a', show ⟦1 * a'⟧ = ⟦a'⟧, by rewrite one_mul)

private proposition qmul_left_inv (a : quotient H) : qmul H (qinv H a) a = qone H :=
quot.induction_on a (λ a', show ⟦a'⁻¹ * a'⟧ = ⟦1⟧, by rewrite mul.left_inv)

protected definition group [instance] : group (quotient H) :=
⦃ group,
  mul          := qmul H,
  inv          := qinv H,
  one          := qone H,
  mul_assoc    := qmul_assoc H,
  mul_one      := qmul_qone H,
  one_mul      := qone_qmul H,
  mul_left_inv := qmul_left_inv H
⦄

-- these theorems characterize the quotient group

definition qproj (a : A) : quotient H := ⟦a⟧

infix ` '* `:65  := λ {A' : Type} [group A'] a H' [is_normal H'], qproj H' a
infix ` / `      := λ {A' : Type} [group A'] G H' [is_normal H'], qproj H' ' G

proposition is_hom_qproj [instance] : is_hom (qproj H) :=
is_mul_hom.mk (λ a b, rfl)

variable {H}

proposition qproj_eq_qproj {a b : A} (h : a * H = b * H) : a '* H = b '* H :=
quot.sound h

proposition lcoset_eq_lcoset_of_qproj_eq_qproj {a b : A} (h : a '* H = b '* H) :  a * H = b * H :=
quot.exact h

variable (H)

proposition qproj_eq_qproj_iff (a b : A) : a '* H = b '* H ↔ a * H = b * H :=
iff.intro lcoset_eq_lcoset_of_qproj_eq_qproj qproj_eq_qproj

proposition ker_qproj [is_subgroup H] : ker (qproj H) = H :=
ext (take a,
  begin
    rewrite [↑ker, mem_set_of_iff, -hom_one (qproj H), qproj_eq_qproj_iff,
      one_lcoset],
    show a * H = H ↔ a ∈ H, from iff.intro mem_of_lcoset_eq_self lcoset_eq_self_of_mem
  end)

proposition qproj_eq_one_iff [is_subgroup H] (a : A) : a '* H = 1 ↔ a ∈ H :=
have H : qproj H a = 1 ↔ a ∈ ker (qproj H), from iff.rfl,
by rewrite [H, ker_qproj]

variable {H}

proposition qproj_eq_one_of_mem [is_subgroup H] {a : A} (aH : a ∈ H) : a '* H = 1 :=
iff.mpr (qproj_eq_one_iff H a) aH

proposition mem_of_qproj_eq_one [is_subgroup H] {a : A} (h : a '* H = 1) : a ∈ H :=
iff.mp (qproj_eq_one_iff H a) h

variable (H)

proposition surjective_qproj : surjective (qproj H) :=
take y, quot.induction_on y (λ a, exists.intro a rfl)

variable {H}

proposition quotient_induction {P : quotient H → Prop} (h : ∀ a, P (a '* H)) : ∀ a, P a :=
quot.ind h

proposition quotient_induction₂ {P : quotient H → quotient H → Prop}
    (h : ∀ a₁ a₂, P (a₁ '* H) (a₂ '* H)) :
  ∀ a₁ a₂, P a₁ a₂ :=
quot.ind₂ h

variable (H)

proposition image_qproj_self [is_subgroup H] : H / H = '{1} :=
eq_of_subset_of_subset
  (image_subset_of_maps_to
    (take x, suppose x ∈ H,
      show x '* H ∈ '{1},
        from mem_singleton_of_eq (qproj_eq_one_of_mem `x ∈ H`)))
  (take x, suppose x ∈ '{1},
    have x = 1, from eq_of_mem_singleton this,
    show x ∈ H / H, by rewrite this; apply mem_image_of_mem _ one_mem)

-- extending a function A → B to a function A / H → B

section respf

variable {H}
variables {f : A → B} (respf : ∀ a₁ a₂, a₁ * H = a₂ * H → f a₁ = f a₂)

definition extend : quotient H → B := quot.lift f respf

proposition extend_qproj (a : A) : extend respf (a '* H) = f a := rfl

proposition extend_comp_qproj : extend respf ∘ (qproj H) = f := rfl

proposition image_extend (G : set A) : (extend respf) ' (G / H) = f ' G :=
by rewrite [-image_comp]

variable [group B]

proposition is_hom_extend [instance] [is_hom f] : is_hom (extend respf) :=
is_mul_hom.mk (take a b,
  show (extend respf (a * b)) = (extend respf a) * (extend respf b), from
    quot.induction_on₂ a b (take a b, hom_mul f a b))

proposition ker_extend : ker (extend respf) = ker f / H :=
eq_of_subset_of_subset
  (quotient_induction
    (take a, assume Ha : qproj H a ∈ ker (extend respf),
      have f a = 1, from Ha,
      show a '* H ∈ ker f / H,
        from mem_image_of_mem _ this))
  (image_subset_of_maps_to
    (take a, assume h : a ∈ ker f,
      show extend respf (a '* H) = 1, from h))

end respf

end quotient_group


/- the first homomorphism theorem for the quotient group -/

namespace quotient_group
  variables [group A] [group B] (f : A → B) [is_hom f]

  lemma eq_of_lcoset_equiv_ker ⦃a b : A⦄ (h : lcoset_equiv (ker f) a b) : f a = f b :=
  have b⁻¹ * a ∈ ker f, from inv_mul_mem_of_lcoset_eq_lcoset h,
  eq.symm (eq_of_inv_mul_mem_ker this)

  definition bar : quotient (ker f) → B := extend (eq_of_lcoset_equiv_ker f)

  proposition bar_qproj (a : A) : bar f (a '* ker f) = f a := rfl

  proposition is_hom_bar [instance] : is_hom (bar f) := is_hom_extend _

  proposition image_bar (G : set A) : bar f ' (G / ker f) = f ' G :=
  by rewrite [↑bar, image_extend]

  proposition image_bar_univ : bar f ' univ = f ' univ :=
  by rewrite [↑bar, -image_eq_univ_of_surjective (surjective_qproj (ker f)),
       image_extend]

  proposition surj_on_bar : surj_on (bar f) univ (f ' univ) :=
  by rewrite [↑surj_on, image_bar_univ]; apply subset.refl

  proposition ker_bar_eq : ker (bar f) = '{1} :=
  by rewrite [↑bar, ker_extend, image_qproj_self]

  proposition injective_bar : injective (bar f) :=
  injective_of_ker_eq_singleton_one (ker_bar_eq f)
end quotient_group


/- a generic morphism extension property -/

section
  variables [group A] [group B] [group C]
  variables (G : set A) [is_subgroup G]
  variables (g : A → C) (f : A → B)

  noncomputable definition gen_extend : C → B := λ c, f (inv_fun g G 1 c)

  variables {G g f}

  proposition eq_of_ker_in_subset {a₁ a₂ : A} (a₁G : a₁ ∈ G) (a₂G : a₂ ∈ G)
      [is_hom_on g G] [is_hom_on f G] (Hker : ker_in g G ⊆ ker f) (H' : g a₁ = g a₂) :
    f a₁ = f a₂ :=
  have memG : a₁⁻¹ * a₂ ∈ G, from mul_mem (inv_mem a₁G) a₂G,
  have a₁⁻¹ * a₂ ∈ ker_in g G, from inv_mul_mem_ker_in_of_eq a₁G a₂G H',
  have a₁⁻¹ * a₂ ∈ ker_in f G, from and.intro (Hker this) memG,
  show f a₁ = f a₂, from eq_of_inv_mul_mem_ker_in a₁G a₂G this

  proposition gen_extend_spec [is_hom_on g G] [is_hom_on f G] (Hker : ker_in g G ⊆ ker f)
    {a : A} (aG : a ∈ G) : gen_extend G g f (g a) = f a :=
  eq_of_ker_in_subset (inv_fun_spec' aG) aG Hker (inv_fun_spec aG)

  proposition is_hom_on_gen_extend [is_hom_on g G] [is_hom_on f G] (Hker : ker_in g G ⊆ ker f) :
    is_hom_on (gen_extend G g f) (g ' G) :=
  have is_subgroup (g ' G), from is_subgroup_image g G,
  take c₁, assume c₁gG : c₁ ∈ g ' G,
  take c₂, assume c₂gG : c₂ ∈ g ' G,
  let ginv := inv_fun g G 1 in
  have Hginv : maps_to ginv (g ' G) G, from maps_to_inv_fun one_mem,
  have ginvc₁ : ginv c₁ ∈ G, from Hginv c₁gG,
  have ginvc₂ : ginv c₂ ∈ G, from Hginv c₂gG,
  have ginvc₁c₂ : ginv (c₁ * c₂) ∈ G, from Hginv (mul_mem c₁gG c₂gG),
  have HH : ∀₀ c ∈ g ' G, g (ginv c) = c,
    from λ a aG, right_inv_on_inv_fun_of_surj_on _ (surj_on_image g G) aG,
  have eq₁ : g (ginv c₁) = c₁, from HH c₁gG,
  have eq₂ : g (ginv c₂) = c₂, from HH c₂gG,
  have eq₃ : g (ginv (c₁ * c₂)) = c₁ * c₂, from HH (mul_mem c₁gG c₂gG),
  have g (ginv (c₁ * c₂)) = g ((ginv c₁) * (ginv c₂)),
    by rewrite [eq₃, hom_on_mul g ginvc₁ ginvc₂, eq₁, eq₂],
  have f (ginv (c₁ * c₂)) = f (ginv c₁ * ginv c₂),
    from eq_of_ker_in_subset (ginvc₁c₂) (mul_mem ginvc₁ ginvc₂) Hker this,
  show f (ginv (c₁ * c₂)) = f (ginv c₁) * f (ginv c₂),
    by rewrite [this, hom_on_mul f ginvc₁ ginvc₂]
end


/- quotient by an arbitrary group, not necessarily normal -/

namespace quotient_group_general

variables [group A] (H : set A) [is_subgroup H]

lemma is_normal_to_group_of_normalizer [instance] :
  is_normal (to_group_of (normalizer H) ' H) :=
have H1 : is_normal_in (to_group_of (normalizer H) ' H)
                       (to_group_of (normalizer H) ' (normalizer H)),
  from is_normal_in_image_image (subset_normalizer_self H) (to_group_of (normalizer H)),
have H2 : to_group_of (normalizer H) ' (normalizer H) = univ,
  from image_to_group_of_eq_univ (normalizer H),
is_normal_of_is_normal_in_univ (by rewrite -H2; exact H1)

section quotient_group
open quotient_group

noncomputable definition quotient : Type := quotient (to_group_of (normalizer H) ' H)

noncomputable definition group_quotient  [instance] : group (quotient H) :=
quotient_group.group (to_group_of (normalizer H) ' H)

noncomputable definition qproj : A → quotient H :=
qproj (to_group_of (normalizer H) ' H) ∘ (to_group_of (normalizer H))

infix ` '* `:65  := λ {A' : Type} [group A'] a H' [is_subgroup H'], qproj H' a
infix ` / `      := λ {A' : Type} [group A'] G H' [is_subgroup H'], qproj H' ' G

proposition is_hom_on_qproj [instance] : is_hom_on (qproj H) (normalizer H) :=
have H₀ : is_hom_on (to_group_of (normalizer H)) (normalizer H),
  from is_hom_on_to_group_of (normalizer H),
have H₁ : is_hom_on (quotient_group.qproj (to_group_of (normalizer H) ' H)) univ,
  from iff.mpr (is_hom_on_univ_iff (quotient_group.qproj (to_group_of (normalizer H) ' H)))
         (is_hom_qproj (to_group_of (normalizer H) ' H)),
is_hom_on_comp H₀ H₁ (maps_to_univ (to_group_of (normalizer H)) (normalizer H))

proposition is_hom_on_qproj' [instance] (G : set A) [is_normal_in H G] :
  is_hom_on (qproj H) G :=
is_hom_on_of_subset (qproj H) (subset_normalizer G H)

proposition ker_in_qproj : ker_in (qproj H) (normalizer H) = H :=
let tg := to_group_of (normalizer H) in
begin
  rewrite [↑ker_in, ker_eq_preimage_one, ↑qproj, preimage_comp, -ker_eq_preimage_one],
  have is_hom_on tg H, from is_hom_on_of_subset _ (subset_normalizer_self H),
  have is_subgroup (tg ' H), from is_subgroup_image tg H,
  krewrite [ker_qproj, to_group_of_preimage_to_group_of_image (subset_normalizer_self H)]
end

end quotient_group

variable {H}

proposition qproj_eq_qproj_iff {a b : A} (Ha : a ∈ normalizer H) (Hb : b ∈ normalizer H) :
   a '* H = b '* H ↔ a * H = b * H :=
by rewrite [lcoset_eq_lcoset_iff, eq_iff_inv_mul_mem_ker_in Ha Hb, ker_in_qproj,
            -inv_mem_iff, mul_inv, inv_inv]

proposition qproj_eq_qproj {a b : A} (Ha : a ∈ normalizer H) (Hb : b ∈ normalizer H)
    (h : a * H = b * H) :
  a '* H = b '* H :=
iff.mpr (qproj_eq_qproj_iff Ha Hb) h

proposition lcoset_eq_lcoset_of_qproj_eq_qproj {a b : A}
    (Ha : a ∈ normalizer H) (Hb : b ∈ normalizer H) (h : a '* H = b '* H) :
  a * H = b * H :=
iff.mp (qproj_eq_qproj_iff Ha Hb) h

variable (H)

proposition qproj_mem {a : A} {G : set A} (aG : a ∈ G) : a '* H ∈ G / H :=
mem_image_of_mem _ aG

proposition qproj_one : 1 '* H = 1 := hom_on_one (qproj H) (normalizer H)

variable {H}

proposition mem_of_qproj_mem {a : A} (anH : a ∈ normalizer H)
    {G : set A} (HsubG : H ⊆ G) [is_subgroup G] [is_normal_in H G]
  (aHGH : a '* H ∈ G / H): a ∈ G :=
have GH : G ⊆ normalizer H, from subset_normalizer G H,
obtain b [bG (bHeq : b '* H = a '* H)], from aHGH,
have b * H = a * H, from lcoset_eq_lcoset_of_qproj_eq_qproj (GH bG) anH bHeq,
have a ∈ b * H, by rewrite this; apply mem_lcoset_self,
have a ∈ b * G, from lcoset_subset_lcoset b HsubG this,
show a ∈ G, by rewrite [lcoset_eq_self_of_mem bG at this]; apply this

proposition qproj_eq_one_iff {a : A} (Ha : a ∈ normalizer H) : a '* H = 1 ↔ a ∈ H :=
by rewrite [-hom_on_one (qproj H) (normalizer H), qproj_eq_qproj_iff Ha one_mem, one_lcoset,
        lcoset_eq_self_iff]

proposition qproj_eq_one_of_mem {a : A} (aH : a ∈ H) : a '* H = 1 :=
iff.mpr (qproj_eq_one_iff (subset_normalizer_self H aH)) aH

proposition mem_of_qproj_eq_one {a : A} (Ha : a ∈ normalizer H) (h : a '* H = 1) : a ∈ H :=
iff.mp (qproj_eq_one_iff Ha) h

variable (H)

section
open quotient_group
proposition surj_on_qproj_normalizer : surj_on (qproj H) (normalizer H) univ :=
have H₀ : surj_on (to_group_of (normalizer H)) (normalizer H) univ,
  from surj_on_to_group_of_univ (normalizer H),
have H₁ : surj_on (quotient_group.qproj (to_group_of (normalizer H) ' H)) univ univ,
  from surj_on_univ_of_surjective univ (surjective_qproj _),
surj_on_comp H₁ H₀
end

variable {H}

proposition quotient_induction {P : quotient H → Prop} (hyp : ∀₀ a ∈ normalizer H, P (a '* H)) :
  ∀ a, P a :=
surj_on_univ_induction (surj_on_qproj_normalizer H) hyp

proposition quotient_induction₂ {P : quotient H → quotient H → Prop}
    (hyp : ∀₀ a₁ ∈ normalizer H, ∀₀ a₂ ∈ normalizer H, P (a₁ '* H) (a₂ '* H)) :
  ∀ a₁ a₂, P a₁ a₂ :=
surj_on_univ_induction₂ (surj_on_qproj_normalizer H) hyp

variable (H)

proposition image_qproj_self : H / H = '{1} :=
eq_of_subset_of_subset
  (image_subset_of_maps_to
    (take x, suppose x ∈ H,
      show x '* H ∈ '{1},
        from mem_singleton_of_eq (qproj_eq_one_of_mem `x ∈ H`)))
  (take x, suppose x ∈ '{1},
    have x = 1, from eq_of_mem_singleton this,
    show x ∈ H / H,
      by rewrite [this, -qproj_one H]; apply mem_image_of_mem _ one_mem)

section respf

variable (H)
variables [group B] (G : set A) [is_subgroup G] (f : A → B)

noncomputable definition extend : quotient H → B := gen_extend G (qproj H) f

variables [is_hom_on f G] [is_normal_in H G]

private proposition aux : is_hom_on (qproj H) G :=
is_hom_on_of_subset (qproj H) (subset_normalizer G H)

local attribute [instance] aux

variables {H f}

private proposition aux' (respf : H ⊆ ker f) : ker_in (qproj H) G ⊆ ker f :=
subset.trans
  (show ker_in (qproj H) G ⊆ ker_in (qproj H) (normalizer H),
    from inter_subset_inter_left _ (subset_normalizer G H))
  (by rewrite [ker_in_qproj]; apply respf)

variable {G}

proposition extend_qproj (respf : H ⊆ ker f) {a : A} (aG : a ∈ G) :
  extend H G f (a '* H) = f a :=
gen_extend_spec (aux' G respf) aG

proposition image_extend (respf : H ⊆ ker f) {s : set A} (ssubG : s ⊆ G) :
  extend H G f ' (s / H) = f ' s :=
begin
  rewrite [-image_comp],
  apply image_eq_image_of_eq_on,
  intro a amems,
  apply extend_qproj respf (ssubG amems)
end

variable (G)

proposition is_hom_on_extend [instance] (respf : H ⊆ ker f) : is_hom_on (extend H G f) (G / H) :=
by unfold extend; apply is_hom_on_gen_extend (aux' G respf)

variable {G}

proposition ker_in_extend [is_subgroup G] (respf : H ⊆ ker f) (HsubG : H ⊆ G) :
  ker_in (extend H G f) (G / H) = (ker_in f G) / H :=
begin
  apply ext,
  intro aH,
  cases surj_on_qproj_normalizer H (show aH ∈ univ, from trivial) with a atemp,
  cases atemp with anH aHeq,
  rewrite -aHeq,
  apply iff.intro,
  { intro akerin,
    cases akerin with aker ain,
    have a '* H ∈ G / H, from ain,
    have a ∈ G, from mem_of_qproj_mem anH HsubG this,
    have a '* H ∈ ker (extend H G f), from aker,
    have extend H G f (a '* H) = 1, from this,
    have f a = extend H G f (a '* H), from eq.symm (extend_qproj respf `a ∈ G`),
    have f a = 1, by rewrite this; assumption,
    have a ∈ ker_in f G, from and.intro this `a ∈ G`,
    show a '* H ∈ (ker_in f G) / H, from qproj_mem H this},
  intro aHker,
  have aker : a ∈ ker_in f G,
    begin
      have Hsub : H ⊆ ker_in f G, from subset_inter respf HsubG,
      have is_normal_in H (ker_in f G),
        from subset.trans (inter_subset_right (ker f) G) (subset_normalizer G H),
      apply (mem_of_qproj_mem anH Hsub aHker)
    end,
  have a ∈ G, from and.right aker,
  have f a = 1, from and.left aker,
  have extend H G f (a '* H) = 1,
    from eq.trans (extend_qproj respf `a ∈ G`) this,
  show a '* H ∈ ker_in (extend H G f) (G / H),
    from and.intro this (qproj_mem H `a ∈ G`)
end

/- (comment from Jeremy)
This version kills the elaborator. I don't know why.
Tracing class instances doesn't show a problem. My best guess is that it is
the backgracking from the "obtain".

proposition ker_in_extend [is_subgroup G] (respf : H ⊆ ker f) (HsubG : H ⊆ G) :
  ker_in (extend H G f) (qproj H ' G) = qproj H ' (ker_in f G) :=
ext (take aH,
  obtain a [(anH : a ∈ normalizer H) (aHeq : a '* H = aH)],
    from surj_on_qproj_normalizer H (show aH ∈ univ, from trivial),
  begin
    rewrite -aHeq, apply iff.intro, unfold ker_in,
    exact
      (assume aker : a '* H ∈ ker (extend H G f) ∩ (qproj H ' G),
        have a '* H ∈ qproj H ' G, from and.right aker,
        have a ∈ G, from mem_of_qproj_mem anH HsubG this,
        -- Uncommenting the next line of code slows things down dramatically.
        -- Uncommenting the one after kills the system.
        -- have a '* H ∈ ker (extend H G f), from and.left aker,
        -- have extend H G f (a '* H) = 1, from this,
        -- have f a = extend H G f (a '* H), from eq.symm (extend_qproj respf `a ∈ G`),
        -- have f a = 1, by rewrite [-this, extend_qproj respf aG],
        -- have a ∈ ker_in f G, from and.intro this `a ∈ G`,
        show a '* H ∈ qproj H ' (ker_in f G), from sorry),
    exact
      (assume hyp : a '* H ∈ qproj H ' (ker_in f G),
        show a '* H ∈ ker_in (extend H G f) (qproj H ' G), from sorry)
  end)
-/

end respf

attribute quotient [irreducible]

end quotient_group_general

/- the first homomorphism theorem for general quotient groups -/

namespace quotient_group_general

variables [group A] [group B] (G : set A) [is_subgroup G]
variables (f : A → B) [is_hom_on f G]

noncomputable definition bar : quotient (ker_in f G) → B :=
extend (ker_in f G) G f

proposition bar_qproj {a : A} (aG : a ∈ G) : bar G f (a '* ker_in f G) = f a :=
extend_qproj (inter_subset_left _ _) aG

proposition is_hom_on_bar [instance] : is_hom_on (bar G f) (G / ker_in f G) :=
have is_subgroup (ker f ∩ G), from is_subgroup_ker_in f G,
have is_normal_in (ker f ∩ G) G, from is_normal_in_ker_in f G,
is_hom_on_extend G (inter_subset_left _ _)

proposition image_bar {s : set A} (ssubG : s ⊆ G) : bar G f ' (s / ker_in f G) = f ' s :=
have is_subgroup (ker f ∩ G), from is_subgroup_ker_in f G,
have is_normal_in (ker f ∩ G) G, from is_normal_in_ker_in f G,
image_extend (inter_subset_left _ _) ssubG

proposition surj_on_bar : surj_on (bar G f) (G / ker_in f G) (f ' G) :=
by rewrite [↑surj_on, image_bar G f (@subset.refl _ G)]; apply subset.refl

proposition ker_in_bar : ker_in (bar G f) (G / ker_in f G) = '{1} :=
have H₀ : ker_in f G ⊆ ker f, from inter_subset_left _ _,
have H₁ : ker_in f G ⊆ G, from inter_subset_right _ _,
by rewrite [↑bar, ker_in_extend H₀ H₁, image_qproj_self]

proposition inj_on_bar : inj_on (bar G f) (G / ker_in f G) :=
inj_on_of_ker_in_eq_singleton_one (ker_in_bar G f)

end quotient_group_general

end group_theory
