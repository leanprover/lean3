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

lemma zero_mul_inf [simp] : 0 * ∞ = 0 := by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos rfl]

lemma inf_mul_zero [simp] : ∞ * 0 = 0 := by rewrite[ereal.mul_comm, zero_mul_inf]

lemma zero_mul_neginf [simp] : 0 * -∞ = 0 := by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos rfl]

lemma neginf_mul_zero [simp] : -∞ * 0 = 0 := by rewrite[ereal.mul_comm, zero_mul_neginf]

-- Preliminary facts --

private lemma mul1 : ∀ x y : ℝ, x * y * ∞ = x * (y * ∞) :=  
take x y,
if X : x = 0 then
   if Y : y = 0 then 
     proof
       have x * y = 0, from X⁻¹ ▸ !zero_mul,
       have of_real x * of_real y = of_real 0, from this ▸ rfl,
       have H : (of_real x * of_real y) * ∞ = of_real 0, from this⁻¹ ▸ zero_mul_inf,
       have H1 : of_real y * ∞ = of_real 0, from Y⁻¹ ▸ zero_mul_inf,
       have of_real x * of_real 0 = of_real 0, from !mul_zero ▸ rfl,
       have of_real x * (of_real y * ∞) = of_real 0, from H1⁻¹ ▸ this,
       show _, from this⁻¹ ▸ H
     qed
   else if Y1 : y > 0 then 
     proof
       have x * y = 0, from X⁻¹ ▸ !zero_mul,
       have of_real x * of_real y = of_real 0, from this ▸ rfl,
       have H : (of_real x * of_real y) * ∞ = of_real 0, from this⁻¹ ▸ zero_mul_inf,
       have H1 : of_real y * ∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_pos Y1],
       have of_real x * (of_real y * ∞) = of_real 0 * ∞, from X ▸ (H1 ▸ rfl),
       have of_real x * (of_real y * ∞) = of_real 0, from this⁻¹ ▸ zero_mul_inf,
       show _, from this⁻¹ ▸ H
     qed
   else 
     proof
       have x * y = 0, from X⁻¹ ▸ !zero_mul,
       have of_real x * of_real y = of_real 0, from this ▸ rfl,
       have H : (of_real x * of_real y) * ∞ = of_real 0, from this⁻¹ ▸ zero_mul_inf,
       have of_real y * ∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_neg Y1],
       have of_real x * (of_real y * ∞) = of_real 0 * -∞, from X ▸ (this ▸ rfl),
       have of_real x * (of_real y * ∞) = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
       show _, from this⁻¹ ▸ H
     qed
   else if X1 : x > 0 then 
     if Y : y = 0 then
       proof
         have x * y = 0, from Y⁻¹ ▸ !mul_zero,
         have of_real x * of_real y = of_real 0, from this ▸ rfl,
         have H : (of_real x * of_real y) * ∞ = of_real 0, from this⁻¹ ▸ zero_mul_inf,
         have H1 : of_real y * ∞ = of_real 0, from Y⁻¹ ▸ zero_mul_inf,
         have of_real x * of_real 0 = of_real (x * 0), by rewrite[*ereal.mul_def, ↑ereal.mul],
         have of_real x * of_real 0 = of_real 0, from !mul_zero ▸ this,
         have of_real x * (of_real y * ∞) = of_real 0, from (H1 ▸ rfl) ▸ this,
         show _, from this⁻¹ ▸ H
       qed
     else if Y1 : y > 0 then 
       proof
         have H : of_real (x * y) * ∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg sorry, if_pos sorry],
         have H1 : of_real y * ∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_pos Y1],
         have of_real x * ∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
         have of_real x * (of_real y * ∞) = ∞, from this ▸ (H1 ▸ rfl),
         show _, from this⁻¹ ▸ H
       qed
     else 
       proof
         have H : of_real (x * y) * ∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg sorry, if_neg sorry],
         have H1 : of_real y * ∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_neg Y1],
         have of_real x * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
         have of_real x * (of_real y * ∞) = -∞, from this ▸ (H1 ▸ rfl),
         show _, from this⁻¹ ▸ H
       qed
   else 
     if Y : y = 0 then
       proof
         have x * y = 0, from Y⁻¹ ▸ !mul_zero,
         have of_real x * of_real y = of_real 0, from this ▸ rfl,
         have H : (of_real x * of_real y) * ∞ = of_real 0, from this⁻¹ ▸ zero_mul_inf,
         have H1 : of_real y * ∞ = of_real 0, from Y⁻¹ ▸ zero_mul_inf,
         have of_real x * of_real 0 = of_real (x * 0), by rewrite[*ereal.mul_def, ↑ereal.mul],
         have of_real x * of_real 0 = of_real 0, from !mul_zero ▸ this,
         have of_real x * (of_real y * ∞) = of_real 0, from (H1 ▸ rfl) ▸ this,
         show _, from this⁻¹ ▸ H
       qed
     else if Y1 : y > 0 then 
       proof
         have H : of_real (x * y) * ∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg sorry, if_neg sorry],
         have H1 : of_real y * ∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_pos Y1],
         have of_real x * ∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
         have of_real x * (of_real y * ∞) = -∞, from this ▸ (H1 ▸ rfl),
         show _, from this⁻¹ ▸ H
       qed
     else 
       proof
         have H : of_real (x * y) * ∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg sorry, if_pos sorry],
         have H1 : of_real y * ∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_neg Y1],
         have of_real x * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
         have of_real x * (of_real y * ∞) = ∞, from this ▸ (H1 ▸ rfl),
         show _, from this⁻¹ ▸ H
       qed

private lemma mul2 : ∀ x y : ℝ, x * y * -∞ = x * (y * -∞) := 
take x y,
if X : x = 0 then 
  if Y : y = 0 then
    proof
       have x * y = 0, from X⁻¹ ▸ !zero_mul,
       have of_real x * of_real y = of_real 0, from this ▸ rfl,
       have H : (of_real x * of_real y) * -∞ = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
       have H1 : of_real y * -∞ = of_real 0, from Y⁻¹ ▸ zero_mul_neginf,
       have of_real x * of_real 0 = of_real 0, from !mul_zero ▸ rfl,
       have of_real x * (of_real y * -∞) = of_real 0, from H1⁻¹ ▸ this,
       show _, from this⁻¹ ▸ H
     qed
  else if Y1 : y > 0 then 
    proof
       have x * y = 0, from X⁻¹ ▸ !zero_mul,
       have of_real x * of_real y = of_real 0, from this ▸ rfl,
       have H : (of_real x * of_real y) * -∞ = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
       have H1 : of_real y * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_pos Y1],
       have of_real x * (of_real y * -∞) = of_real 0 * -∞, from X ▸ (H1 ▸ rfl),
       have of_real x * (of_real y * -∞) = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
       show _, from this⁻¹ ▸ H
     qed
  else 
    proof
       have x * y = 0, from X⁻¹ ▸ !zero_mul,
       have of_real x * of_real y = of_real 0, from this ▸ rfl,
       have H : (of_real x * of_real y) * -∞ = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
       have of_real y * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_neg Y1],
       have of_real x * (of_real y * -∞) = of_real 0 * ∞, from X ▸ (this ▸ rfl),
       have of_real x * (of_real y * -∞) = of_real 0, from this⁻¹ ▸ zero_mul_inf,
       show _, from this⁻¹ ▸ H
     qed
else if X1: x > 0 then
  if Y : y = 0 then 
    proof
      have x * y = 0, from Y⁻¹ ▸ !mul_zero,
      have of_real x * of_real y = of_real 0, from this ▸ rfl,
      have H : (of_real x * of_real y) * -∞ = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
      have H1 : of_real y * -∞ = of_real 0, from Y⁻¹ ▸ zero_mul_neginf,
      have of_real x * of_real 0 = of_real (x * 0), by rewrite[*ereal.mul_def, ↑ereal.mul],
      have of_real x * of_real 0 = of_real 0, from !mul_zero ▸ this,
      have of_real x * (of_real y * -∞) = of_real 0, from (H1 ▸ rfl) ▸ this,
      show _, from this⁻¹ ▸ H
    qed    
  else if Y1 : y > 0 then 
    proof
      have H : of_real (x * y) * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg sorry, if_pos sorry],
      have H1 : of_real y * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_pos Y1],
      have of_real x * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
      have of_real x * (of_real y * -∞) = -∞, from this ▸ (H1 ▸ rfl),
      show _, from this⁻¹ ▸ H
    qed
  else 
    proof
      have H : of_real (x * y) * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg sorry, if_neg sorry],
      have H1 : of_real y * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_neg Y1],
      have of_real x * ∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
      have of_real x * (of_real y * -∞) = ∞, from this ▸ (H1 ▸ rfl),
      show _, from this⁻¹ ▸ H
    qed
else 
  if Y : y = 0 then
    proof
      have x * y = 0, from Y⁻¹ ▸ !mul_zero,
      have of_real x * of_real y = of_real 0, from this ▸ rfl,
      have H : (of_real x * of_real y) * -∞ = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
      have H1 : of_real y * -∞ = of_real 0, from Y⁻¹ ▸ zero_mul_neginf,
      have of_real x * of_real 0 = of_real (x * 0), by rewrite[*ereal.mul_def, ↑ereal.mul],
      have of_real x * of_real 0 = of_real 0, from !mul_zero ▸ this,
      have of_real x * (of_real y * -∞) = of_real 0, from (H1 ▸ rfl) ▸ this,
      show _, from this⁻¹ ▸ H
    qed
  else if Y1 : y > 0 then 
    proof
      have H : of_real (x * y) * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg sorry, if_neg sorry],
      have H1 : of_real y * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_pos Y1],
      have of_real x * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
      have of_real x * (of_real y * -∞) = ∞, from this ▸ (H1 ▸ rfl),
      show _, from this⁻¹ ▸ H
    qed
  else 
    proof
      have H : of_real (x * y) * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg sorry, if_pos sorry],
      have H1 : of_real y * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg Y, if_neg Y1],
      have of_real x * ∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
      have of_real x * (of_real y * -∞) = -∞, from this ▸ (H1 ▸ rfl),
      show _, from this⁻¹ ▸ H
    qed

private lemma mul3 : ∀ x : ℝ, x * ∞ * ∞ = x * (∞ * ∞) := 
take x,
if X : x = 0 then 
  have of_real x * ∞ = of_real 0, from X⁻¹ ▸ zero_mul_inf,
  have H : of_real x * ∞ * ∞ = of_real 0, from this⁻¹ ▸ zero_mul_inf,
  have of_real x * (∞ * ∞) = of_real 0, by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos X],
  show _, from this⁻¹ ▸ H
else if X1 : x > 0 then 
   by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1]
else 
   by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1]

private lemma mul4 : ∀ x : ℝ, x * -∞ * -∞ = x * (-∞ * -∞) := 
take x,
if X : x = 0 then
  have of_real x * -∞ = of_real 0, from X⁻¹ ▸ zero_mul_neginf,
  have H : of_real x * -∞ * -∞ = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
  have of_real x * (-∞ * -∞) = of_real 0, by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos X],
  show _, from this⁻¹ ▸ H
else if X1 : x > 0 then 
  have H : (of_real x * -∞) * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  have of_real x * (-∞ * -∞) = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  show _, from this⁻¹ ▸ H
else 
  have H : (of_real x * -∞) * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  have of_real x * (-∞ * -∞) = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  show _, from this⁻¹ ▸ H 

private lemma mul5 : ∀ x : ℝ, x * ∞ * -∞ = x * (∞ * -∞) := 
take x,
if X : x = 0 then 
  have of_real x * ∞ = of_real 0, from X⁻¹ ▸ zero_mul_inf,
  have H : of_real x * ∞ * -∞ = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
  have of_real x * (∞ * -∞) = of_real 0, by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos X],
  show _, from this⁻¹ ▸ H
else if X1 : x > 0 then 
  have H : (of_real x * ∞) * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  have of_real x * (∞ * -∞) = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  show _, from this⁻¹ ▸ H
else 
  have H : (of_real x * ∞) * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  have of_real x * (∞ * -∞) = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  show _, from this⁻¹ ▸ H

private lemma mul6 : ∀ x : ℝ, ∞ * x * -∞ = ∞ * (x * -∞) := 
take x,
if X : x = 0 then 
  have ∞ * of_real x = of_real 0, by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos X],
  have H : ∞ * of_real x * -∞ = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
  have of_real x * -∞ = of_real 0, from X⁻¹ ▸ zero_mul_neginf,
  have ∞ * (of_real x * -∞) = of_real 0, from this⁻¹ ▸ inf_mul_zero,
  show _, from this⁻¹ ▸ H
else if X1 : x > 0 then 
  have ∞ * of_real x = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  have H : ∞ * of_real x * -∞ = -∞, from this⁻¹ ▸ rfl,
  have of_real x * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  have ∞ * (of_real x * -∞) = -∞, from this⁻¹ ▸ rfl,
  show _, from this⁻¹ ▸ H
else 
  have ∞ * of_real x = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  have H : ∞ * of_real x * -∞ = ∞, from this⁻¹ ▸ rfl,
  have of_real x * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  have ∞ * (of_real x * -∞) = ∞, from this⁻¹ ▸ rfl,
  show _, from this⁻¹ ▸ H

private lemma mul7 : ∀ x : ℝ, ∞ * x * ∞ = ∞ * (x * ∞) := 
take x,
if X : x = 0 then
  have ∞ * of_real x = of_real 0, by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos X],
  have H : ∞ * of_real x * ∞ = of_real 0, from this⁻¹ ▸ zero_mul_inf,
  have of_real x * ∞ = of_real 0, by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos X],
  have ∞ * (of_real x * ∞) = of_real 0, from this⁻¹ ▸ inf_mul_zero,
  show _, from this⁻¹ ▸ H
else if X1 : x > 0 then 
  have ∞ * of_real x = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  have H : ∞ * of_real x * ∞ = ∞, from this⁻¹ ▸ rfl,
  have of_real x * ∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  have ∞ * (of_real x * ∞) = ∞, from this⁻¹ ▸ rfl,
  show _, from this⁻¹ ▸ H
else 
  have ∞ * of_real x = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  have H : ∞ * of_real x * ∞ = -∞, from this⁻¹ ▸ rfl,
  have of_real x * ∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  have ∞ * (of_real x * ∞) = -∞, from this⁻¹ ▸ rfl,
  show _, from this⁻¹ ▸ H

private lemma mul8 : ∀ x : ℝ, -∞ * x * -∞ = -∞ * (x * -∞) := 
take x,
if X : x = 0 then 
  have -∞ * of_real x = of_real 0, by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos X],
  have H : -∞ * of_real x * -∞ = of_real 0, from this⁻¹ ▸ zero_mul_neginf,
  have of_real x * -∞ = of_real 0, by rewrite[*ereal.mul_def, ↑ereal.mul, if_pos X],
  have -∞ * (of_real x * -∞) = of_real 0, from this⁻¹ ▸ neginf_mul_zero,
  show _, from this⁻¹ ▸ H
else if X1 : x > 0 then 
  have -∞ * of_real x = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  have H : -∞ * of_real x * -∞ = ∞, from this⁻¹ ▸ rfl,
  have of_real x * -∞ = -∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_pos X1],
  have -∞ * (of_real x * -∞) = ∞, from this⁻¹ ▸ rfl,
  show _, from this⁻¹ ▸ H
else 
  have -∞ * of_real x = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  have H : -∞ * of_real x * -∞ = -∞, from this⁻¹ ▸ rfl,
  have of_real x * -∞ = ∞, by rewrite[*ereal.mul_def, ↑ereal.mul, if_neg X, if_neg X1],
  have -∞ * (of_real x * -∞) = -∞, from this⁻¹ ▸ rfl,
  show _, from this⁻¹ ▸ H

protected theorem mul_assoc : ∀ u v w : ereal, (u * v) * w = u * (v * w) 
| (of_real x) (of_real y) (of_real z) := congr_arg of_real !mul.assoc
| (of_real x) (of_real y) ∞           := !mul1
| (of_real x) (of_real y) -∞          := !mul2
| (of_real x) ∞ (of_real z)           := by rewrite[ereal.mul_comm x, ereal.mul_comm, ereal.mul_comm ∞, -mul1, ereal.mul_comm,
                                            ereal.mul_comm z, ereal.mul_comm, mul1]
| (of_real x) ∞ ∞                     := !mul3
| (of_real x) ∞ -∞                    := !mul5
| (of_real x) -∞ (of_real z)          := by rewrite[ereal.mul_comm, -!mul2, ereal.mul_comm z, mul2]
| (of_real x) -∞ ∞                    := by rewrite[ereal.mul_comm, -!mul6, ereal.mul_comm ∞, mul5]
| (of_real x) -∞ -∞                   := !mul4
| ∞ (of_real y) (of_real z)           := by rewrite[ereal.mul_comm, ereal.mul_comm ∞, -mul1, ereal.mul_comm, ereal.mul_comm y]
| ∞ (of_real y) ∞                     := !mul7
| ∞ (of_real y) -∞                    := !mul6
| ∞ ∞ (of_real z)                     := by rewrite[ereal.mul_comm, -!mul3]
| ∞ ∞ ∞                               := rfl
| ∞ ∞ -∞                              := rfl
| ∞ -∞ (of_real z)                    := by rewrite[ereal.mul_comm, -mul5, ereal.mul_comm z, mul6]
| ∞ -∞ ∞                              := by rewrite[*ereal.mul_def, ↑ereal.mul]  
| ∞ -∞ -∞                             := by rewrite[*ereal.mul_def, ↑ereal.mul] 
| -∞ (of_real y) (of_real z)          := by rewrite[ereal.mul_comm, ereal.mul_comm -∞, -mul2, ereal.mul_comm, ereal.mul_comm y]
| -∞ (of_real y) ∞                    := by rewrite[ereal.mul_comm -∞, ereal.mul_comm, -mul6]
| -∞ (of_real y) -∞                   := !mul8
| -∞ ∞ (of_real z)                    := by rewrite[ereal.mul_comm, ereal.mul_comm -∞, -mul5]
| -∞ ∞ ∞                              := rfl
| -∞ ∞ -∞                             := rfl
| -∞ -∞ (of_real z)                   := by rewrite[ereal.mul_comm, -mul4]
| -∞ -∞ ∞                             := by rewrite[*ereal.mul_def, ↑ereal.mul]  
| -∞ -∞ -∞                            := by rewrite[*ereal.mul_def, ↑ereal.mul]  

protected theorem one_mul : ∀ u : ereal, of_real 1 * u = u
| (of_real x) := !real.one_mul ▸ rfl
| ∞           := sorry 
| -∞          := sorry

protected theorem mul_one : ∀ u : ereal, u * 1 = u := 
  begin
    intro u,
    rewrite[ereal.mul_comm],
    exact !ereal.one_mul
  end

end ereal

namespace ereal_order

open ereal
 
noncomputable protected definition le : ereal → ereal → Prop
| (of_real x) (of_real y) := if x < y then true else false
| (of_real x) ∞           := true
| (of_real x) -∞          := false
| ∞ (of_real y)           := false
| ∞ ∞                     := false
| ∞ -∞                    := false
| -∞ (of_real y)          := true
| -∞ ∞                    := true
| -∞ -∞                   := false

infix `<`:= ereal_order.le

noncomputable protected definition leq : ereal → ereal → Prop := λ x, λ y, x < y ∨ x = y

infix `≤` := ereal_order.leq

noncomputable protected definition ge : ereal → ereal → Prop
| (of_real x) (of_real y) := if x > y then true else false
| (of_real x) ∞           := false
| (of_real x) -∞          := true
| ∞ (of_real y)           := true
| ∞ ∞                     := false
| ∞ -∞                    := true
| -∞ (of_real y)          := false
| -∞ ∞                    := false
| -∞ -∞                   := false

infix `>` := ereal_order.ge

noncomputable protected definition geq : ereal → ereal → Prop := λ x, λ y, x > y ∨ x = y

infix `≥` := ereal_order.geq

end ereal_order

namespace nnereal

open ereal ereal_order

record nnereal : Type :=
(r : ereal) (nn : r ≥ 0)

attribute nnereal.r [coercion]

end nnereal

