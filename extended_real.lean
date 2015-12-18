import data.real data.set data.nat 
open real algebra eq.ops nat classical

inductive ereal : Type :=
| of_real : ℝ → ereal
| infty : ereal
| neginfty : ereal

notation `∞` := ereal.infty
notation `-∞` := ereal.neginfty

namespace ereal 

attribute ereal.of_real [coercion]

definition ereal_has_zero [reducible] [instance] [priority real.prio] : has_zero ereal :=
has_zero.mk (of_real 0)

definition complex_has_one [reducible] [instance] [priority real.prio] : has_one ereal :=
has_one.mk (of_real 1)

protected definition add : ereal → ereal → ereal
| (of_real x) (of_real y) := of_real (x + y)
| (of_real x) ∞           := ∞
| (of_real x) -∞          := -∞
| ∞ (of_real y)           := ∞
| ∞ ∞                     := ∞
| ∞ -∞                    := ∞
| -∞ (of_real y)          := -∞
| -∞ ∞                    := ∞
| -∞ -∞                   := -∞

noncomputable protected definition mul : ereal → ereal → ereal
| (of_real x) (of_real y) := of_real (x * y)
| (of_real x) ∞           := if x = 0 then of_real 0 else if x > 0 then ∞ else -∞
| (of_real x) -∞          := if x = 0 then of_real 0 else if x > 0 then -∞ else ∞
| ∞ (of_real y)           := if y = 0 then of_real 0 else if y > 0 then ∞ else -∞
| ∞ ∞                     := ∞
| ∞ -∞                    := -∞
| -∞ (of_real y)          := if y = 0 then of_real 0 else if y > 0 then -∞ else ∞
| -∞ ∞                    := -∞
| -∞ -∞                   := ∞

protected definition neg : ereal → ereal
| (of_real x) := of_real (-x)
| ∞           := -∞
| -∞          := ∞

definition ereal_has_add [reducible] [instance] [priority real.prio] :
  has_add ereal :=
has_add.mk ereal.add

noncomputable definition ereal_has_mul [reducible] [instance] [priority real.prio] :
  has_mul ereal :=
has_mul.mk ereal.mul

definition ereal_has_neg [reducible] [instance] [priority real.prio] :
  has_neg ereal :=
has_neg.mk ereal.neg

protected theorem add_def (x y : ereal) : x + y = ereal.add x y := rfl

protected theorem mul_def (x y : ereal) : x * y = ereal.mul x y := rfl

protected theorem neg_def (x : ereal) : -x = ereal.neg x := rfl

protected theorem add_comm : ∀ u v : ereal, u + v = v + u
| (of_real x) (of_real y) := congr_arg of_real !add.comm
| (of_real x) ∞           := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) -∞          := by rewrite[*ereal.add_def, ↑ereal.add]
| ∞ (of_real y)           := by rewrite[*ereal.add_def, ↑ereal.add]
| ∞ ∞                     := rfl
| ∞ -∞                    := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ (of_real y)          := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ ∞                    := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ -∞                   := rfl

protected theorem add_assoc : ∀ u v w : ereal, (u + v) + w = u + (v + w) 
| (of_real x) (of_real y) (of_real z) := congr_arg of_real !add.assoc
| (of_real x) (of_real y) ∞           := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) (of_real y) -∞          := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) ∞ (of_real z)           := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) ∞ ∞                     := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) ∞ -∞                    := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) -∞ (of_real z)          := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) -∞ ∞                    := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) -∞ -∞                   := by rewrite[*ereal.add_def, ↑ereal.add]
| ∞ (of_real y) (of_real z)           := by rewrite[*ereal.add_def, ↑ereal.add]
| ∞ (of_real y) ∞                     := rfl
| ∞ (of_real y) -∞                    := rfl
| ∞ ∞ (of_real z)                     := by rewrite[*ereal.add_def, ↑ereal.add]
| ∞ ∞ ∞                               := rfl
| ∞ ∞ -∞                              := by rewrite[*ereal.add_def, ↑ereal.add]
| ∞ -∞ (of_real z)                    := by rewrite[*ereal.add_def, ↑ereal.add]
| ∞ -∞ ∞                              := by rewrite[*ereal.add_def, ↑ereal.add]
| ∞ -∞ -∞                             := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ (of_real y) (of_real z)          := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ (of_real y) ∞                    := rfl
| -∞ (of_real y) -∞                   := rfl
| -∞ ∞ (of_real z)                    := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ ∞ ∞                              := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ ∞ -∞                             := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ -∞ (of_real z)                   := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ -∞ ∞                             := by rewrite[*ereal.add_def, ↑ereal.add] 
| -∞ -∞ -∞                            := rfl

protected theorem zero_add : ∀ u : ereal, 0 + u = u 
| (of_real x) := congr_arg of_real !real.zero_add
| ∞           := rfl
| -∞          := rfl

protected theorem add_zero : ∀ u : ereal, u + 0 = u :=
  begin
    intro u,
    rewrite[ereal.add_comm],
    exact !ereal.zero_add
  end

protected theorem mul_comm : ∀ u v : ereal, u * v = v * u
| (of_real x) (of_real y) := congr_arg of_real !mul.comm
| (of_real x) ∞           := if H : x = 0 then
                                by rewrite [*ereal.mul_def, ↑ereal.mul, *if_pos H]
                             else if H1 : x > 0 then
                                by rewrite [*ereal.mul_def, ↑ereal.mul, *if_neg H, *if_pos H1]
                             else
                                by rewrite [*ereal.mul_def, ↑ereal.mul, *if_neg H, *if_neg H1]
| (of_real x) -∞          := if H : x = 0 then 
                                by rewrite [*ereal.mul_def, ↑ereal.mul, *if_pos H]
                             else if H1 : x > 0 then 
                                by rewrite [*ereal.mul_def, ↑ereal.mul, *if_neg H, *if_pos H1]
                             else 
                               by rewrite [*ereal.mul_def, ↑ereal.mul, *if_neg H, *if_neg H1]
|  ∞ (of_real y)          := if H : y = 0 then 
                                by rewrite [*ereal.mul_def, ↑ereal.mul, *if_pos H]
                             else if H1 : y > 0 then 
                                by rewrite [*ereal.mul_def, ↑ereal.mul, *if_neg H, *if_pos H1]
                             else 
                               by rewrite [*ereal.mul_def, ↑ereal.mul, *if_neg H, *if_neg H1]
| ∞ ∞                     := rfl
| ∞ -∞                    := by rewrite[*ereal.mul_def, ↑ereal.mul]
| -∞ (of_real y)          := if H : y = 0 then 
                                by rewrite [*ereal.mul_def, ↑ereal.mul, *if_pos H]
                             else if H1 : y > 0 then 
                                by rewrite [*ereal.mul_def, ↑ereal.mul, *if_neg H, *if_pos H1]
                             else 
                               by rewrite [*ereal.mul_def, ↑ereal.mul, *if_neg H, *if_neg H1]
| -∞ ∞                    := by rewrite[*ereal.mul_def, ↑ereal.mul]
| -∞ -∞                   := rfl

-- preliminay facts --

lemma zero_mul_inf : 0 * ∞ = 0 := by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos rfl]

lemma inf_mul_zero : ∞ * 0 = 0 := by rewrite[ereal.mul_comm, zero_mul_inf]

lemma zero_mul_neginf : 0 * -∞ = 0 := by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos rfl]

lemma neginf_mul_zero : -∞ * 0 = 0 := by rewrite[ereal.mul_comm, zero_mul_neginf]

private lemma mul1 : ∀ x y : ℝ, x * y * ∞ = x * (y * ∞) := sorry
private lemma mul2 : ∀ x y : ℝ, x * y * -∞ = x * (y * -∞) := sorry
private lemma mul3 : ∀ x y : ℝ, ∞ * x * y = ∞ * (x * y) := sorry
private lemma mul4 : ∀ x y : ℝ, -∞ * x * y = -∞ * (x * y) := sorry
private lemma mul5 : ∀ x : ℝ, x * ∞ * ∞ = x * (∞ * ∞) := sorry
private lemma mul6 : ∀ x : ℝ, x * -∞ * -∞ = x * (-∞ * -∞) := sorry
private lemma mul7 : ∀ x : ℝ, x * ∞ * -∞ = x * (∞ * -∞) := sorry
private lemma mul8 : ∀ x : ℝ, ∞ * x * -∞ = ∞ * (x * -∞) := sorry
private lemma mul9 : ∀ x : ℝ, ∞ * x * ∞ = ∞ * (x * ∞) := sorry
private lemma mul10 : ∀ x : ℝ, -∞ * x * -∞ = -∞ * (x * -∞) := sorry

protected theorem mul_assoc : ∀ u v w : ereal, (u * v) * w = u * (v * w) 
| (of_real x) (of_real y) (of_real z) := congr_arg of_real !mul.assoc
| (of_real x) (of_real y) ∞           := !ereal.mul1
| (of_real x) (of_real y) -∞          := !ereal.mul2
| (of_real x) ∞ (of_real z)           := by rewrite[ereal.mul_comm x, ereal.mul3, ereal.mul_comm, ereal.mul1]
| (of_real x) ∞ ∞                     := !ereal.mul5
| (of_real x) ∞ -∞                    := !ereal.mul7
| (of_real x) -∞ (of_real z)          := by rewrite[ereal.mul_comm, -ereal.mul2, ereal.mul_comm z, ereal.mul2]
| (of_real x) -∞ ∞                    := by rewrite[ereal.mul_comm, -ereal.mul8, ereal.mul_comm ∞, ereal.mul7]
| (of_real x) -∞ -∞                   := !ereal.mul6
| ∞ (of_real y) (of_real z)           := !ereal.mul3
| ∞ (of_real y) ∞                     := !ereal.mul9
| ∞ (of_real y) -∞                    := !ereal.mul8
| ∞ ∞ (of_real z)                     := by rewrite[ereal.mul_comm, -ereal.mul5]
| ∞ ∞ ∞                               := rfl
| ∞ ∞ -∞                              := rfl
| ∞ -∞ (of_real z)                    := by rewrite[ereal.mul_comm, -ereal.mul7, ereal.mul_comm z, ereal.mul8]
| ∞ -∞ ∞                              := by rewrite[*ereal.mul_def, ↑ereal.mul]  
| ∞ -∞ -∞                             := by rewrite[*ereal.mul_def, ↑ereal.mul] 
| -∞ (of_real y) (of_real z)          := !ereal.mul4
| -∞ (of_real y) ∞                    := by rewrite[ereal.mul_comm -∞, ereal.mul_comm, -ereal.mul8]
| -∞ (of_real y) -∞                   := !ereal.mul10
| -∞ ∞ (of_real z)                    := by rewrite[ereal.mul_comm, ereal.mul_comm -∞, -ereal.mul7]
| -∞ ∞ ∞                              := rfl
| -∞ ∞ -∞                             := rfl
| -∞ -∞ (of_real z)                   := by rewrite[ereal.mul_comm, -ereal.mul6]
| -∞ -∞ ∞                             := by rewrite[*ereal.mul_def, ↑ereal.mul]  
| -∞ -∞ -∞                            := by rewrite[*ereal.mul_def, ↑ereal.mul]  

protected theorem one_mul : ∀ u : ereal, of_real 1 * u = u
| (of_real x) := !real.one_mul ▸ rfl
| ∞           := sorry -- Prove ¬(1 = 0) and 1 > 0 --
| -∞          := sorry

protected theorem mul_one : ∀ u : ereal, u * 1 = u := 
  begin
    intro u,
    rewrite[ereal.mul_comm],
    exact !ereal.one_mul
  end

protected theorem left_distrib : ∀ u v w : ereal, u * (v + w) = u * v + u * w 
| (of_real x) (of_real y) (of_real z) := sorry
| (of_real x) (of_real y) ∞           := sorry
| (of_real x) (of_real y) -∞          := sorry
| (of_real x) ∞ (of_real z)           := sorry
| (of_real x) ∞ ∞                     := sorry
| (of_real x) ∞ -∞                    := sorry
| (of_real x) -∞ (of_real z)          := sorry
| (of_real x) -∞ ∞                    := sorry
| (of_real x) -∞ -∞                   := sorry
| ∞ (of_real y) (of_real z)           := sorry
| ∞ (of_real y) ∞                     := sorry
| ∞ (of_real y) -∞                    := sorry
| ∞ ∞ (of_real z)                     := sorry
| ∞ ∞ ∞                               := rfl
| ∞ ∞ -∞                              := sorry
| ∞ -∞ (of_real z)                    := sorry
| ∞ -∞ ∞                              := sorry
| ∞ -∞ -∞                             := rfl
| -∞ (of_real y) (of_real z)          := sorry
| -∞ (of_real y) ∞                    := sorry
| -∞ (of_real y) -∞                   := sorry 
| -∞ ∞ (of_real z)                    := sorry 
| -∞ ∞ ∞                              := rfl
| -∞ ∞ -∞                             := sorry
| -∞ -∞ (of_real z)                   := sorry
| -∞ -∞ ∞                             := sorry
| -∞ -∞ -∞                            := rfl

protected theorem right_distrib : ∀ u v w : ereal, (u + v) * w = u * w + v * w := 
  begin
    intro u v w,
    rewrite[ereal.mul_comm, ereal.left_distrib, *ereal.mul_comm w]
  end

end ereal

namespace ereal_order

open ereal

noncomputable protected definition leq : ereal → ereal → Prop
| (of_real x) (of_real y) := if x ≤ y then true else false
| (of_real x) ∞           := true
| (of_real x) -∞          := false
| ∞ (of_real y)           := false
| ∞ ∞                     := true
| ∞ -∞                    := false
| -∞ (of_real y)          := true
| -∞ ∞                    := true
| -∞ -∞                   := true

infix `≤`:= ereal_order.leq

noncomputable protected definition geq : ereal → ereal → Prop
| (of_real x) (of_real y) := if x ≥ y then true else false
| (of_real x) ∞           := false
| (of_real x) -∞          := true
| ∞ (of_real y)           := true
| ∞ ∞                     := true
| ∞ -∞                    := true
| -∞ (of_real y)          := false
| -∞ ∞                    := false
| -∞ -∞                   := true

infix `≥` := ereal_order.geq

end ereal_order

namespace nnereal

open ereal ereal_order

record nnereal : Type :=
(r : ereal) (nn : r ≥ 0)

attribute nnereal.r [coercion]

end nnereal

