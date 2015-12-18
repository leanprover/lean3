import data.real data.set data.nat algebra.group_bigops algebra.group_set_bigops
open real eq.ops set nat 

variable {X : Type}

namespace measure

namespace sigma_algebra

structure sigma_algebra (X : Type) :=
  (space : set X) 
  (sets : set (set X))
  (subs : (∀ S : set X, S ∈ sets → S ⊆ space))
  (entire : space ∈ sets)
  (complements : ∀A, A ∈ sets → (-A ∈ sets))
  (unions : ∀ U : ℕ → set X, (∀ i : ℕ, (U i ∈ sets)) → Union U ∈ sets)

attribute sigma_algebra [class]
attribute sigma_algebra.sets [coercion]

abbreviation space := @sigma_algebra.space
abbreviation sets := @sigma_algebra.sets

definition measurable [M : sigma_algebra X] (S : set X) : Prop := S ∈ M

definition measurable_collection [M : sigma_algebra X] (S : set (set X)) : Prop :=  ∀ s, s ∈ S → measurable s

definition measurable_sequence [M : sigma_algebra X] (A : ℕ → set X) : Prop := ∀ i, measurable (A i)

lemma space_closed {M : sigma_algebra X} (S : set X) (MS : measurable S) : ∀ x : X, x ∈ S → x ∈ (space M) := 
  take x, 
  suppose x ∈ S,
  have S ⊆ space M, from sigma_algebra.subs M S MS,
  show x ∈ space M, from mem_of_subset_of_mem this `x ∈ S`

theorem sigma_empty {M : sigma_algebra X} : ∅ ∈ M :=
 (eq_empty_of_forall_not_mem 
    (take x,
    not.intro(λ H,
      (not_mem_of_mem_comp H) 
      ((space_closed (-(space M)) ((sigma_algebra.complements M (space M)) (sigma_algebra.entire M)) x) H))))
        ▸ (sigma_algebra.complements M (space M)) (sigma_algebra.entire M)

lemma countable_com  {M : sigma_algebra X} (U : ℕ → set X) : (∀ i, U i ∈ M) → (∀ j, -(U j) ∈ M) := 
  suppose ∀ i, U i ∈ M, 
  take j, 
  show -(U j) ∈ M, from !sigma_algebra.complements !this

definition comp_family [reducible] (U : ℕ → set X) : ℕ → set X := λ i, -(U i)

prefix `-` := comp_family

section 

  open classical

  lemma Inter_eq (U : ℕ → set X) : Inter U = -(Union (-U)) := 
    ext(take x, iff.intro
      (suppose x ∈ Inter U,
       show x ∈ -(Union (-U)), from not.intro(λ t, obtain i (Hi : x ∉ (U i)), from t, Hi (this i)))        
      (suppose x ∈ -(Union (-U)),
        show x ∈ Inter U, from 
          take i,
          not_not_elim (((iff.elim_left !forall_iff_not_exists) this) i)))

end 

theorem Inter_in_sets {M : sigma_algebra X} (U : ℕ → set X) (Um : ∀ i, measurable (U i)) :
  measurable (Inter U) := 
!Inter_eq⁻¹ ▸ (!sigma_algebra.complements (!sigma_algebra.unions (!countable_com Um)))

definition bin_extension [reducible] [M : sigma_algebra X] (U₀ U₁ : set X) : ℕ → set X := λ i, (if i ≤ 1 then (if i = 0 then U₀ else U₁) else ∅)

 lemma extension_measurable {M : sigma_algebra X} (U₀ U₁ : set X) (s₁ : measurable U₀) (s₂ : measurable U₁) :
   ∀ i : ℕ, measurable (bin_extension U₀ U₁ i) :=
  take i,
  decidable.by_cases
  (suppose leq : i ≤ 1, 
    decidable.by_cases
      (suppose i = 0, 
        begin
          unfold bin_extension,
          rewrite[if_pos leq, if_pos this],
          exact s₁
        end)
      (suppose ¬(i = 0), 
        begin
          unfold bin_extension,
          rewrite[if_pos leq, if_neg this],
          exact s₂
        end))
  (suppose ¬(i ≤ 1), 
    begin
      unfold bin_extension,
      rewrite[if_neg this],
      exact sigma_empty
    end)


lemma bin_union {M : sigma_algebra X} (U₀ U₁ : set X) (s₁ : measurable U₀) (s₂ : measurable U₁) : 
  measurable (U₀ ∪ U₁) :=
(ext(λx, iff.intro 
  (λ H, obtain i (Hi : x ∈ (bin_extension U₀ U₁) i), from H,
   assert H : (i ≤ 1), from not_not_elim
     (not.intro(suppose ¬(i ≤ 1),
       have H₁ : (bin_extension U₀ U₁) i = ∅, 
         begin
           unfold bin_extension,
           rewrite[if_neg this]
         end,
       !mem_empty_eq ▸ H₁ ▸ Hi)),
   decidable.by_cases
     (suppose i = 0, !mem_union_left (this ▸ Hi)) 
     (λ s, !mem_union_right
         ((begin
           unfold bin_extension,
           rewrite[if_pos H, if_neg s]
          end)
        ▸ Hi)))
  (λ H, assert A : U₀ ∪ U₁ ⊆ Union (bin_extension U₀ U₁), from
     take x,
     assume t,
       or.elim (mem_or_mem_of_mem_union t) 
         (λ y, exists.intro 0 y)
         (λ z, exists.intro 1 z),
   (!mem_of_subset_of_mem A) H))) ▸ ((sigma_algebra.unions M (bin_extension U₀ U₁)) (extension_measurable U₀ U₁ s₁ s₂))

definition bin_extension' [M : sigma_algebra X] (U₀ U₁ : set X) : ℕ → set X := λ i, if i = 0 then U₀ else U₁

lemma extension'_in_sets {M : sigma_algebra X} (U₀ U₁ : set X) (s₁ : measurable U₀) (s₂ : measurable U₁) :
  ∀ i : ℕ, (bin_extension' U₀ U₁) i ∈ M :=
take i,
 if H : i = 0 then
     begin
       unfold bin_extension',
       rewrite[if_pos H],
       exact s₁
     end
  else
     begin
       unfold bin_extension',
       rewrite[if_neg H],
       exact s₂
     end

theorem bin_inter {M : sigma_algebra X} (U₀ U₁ : set X) (s₀ : measurable U₀) (s₁ : measurable U₁) :
  measurable (U₀ ∩ U₁) := 
have U₀ ∩ U₁ =  Inter (bin_extension' U₀ U₁), from ext(λx, iff.intro 
    (suppose S : x ∈ U₀ ∩ U₁, take i,
          decidable.by_cases
            (suppose i = 0, 
              (this⁻¹ ▸ rfl)⁻¹ ▸ and.elim_left (rfl ▸ S))
            (suppose ¬(i = 0),
             have (bin_extension' U₀ U₁) i = U₁, 
               begin
                 unfold bin_extension',
                 rewrite[if_neg this]
               end,
              this⁻¹ ▸ and.elim_right (rfl ▸ S)))
    (suppose x ∈ Inter (bin_extension' U₀ U₁) , and.intro (this 0) (this 1))), 
  this⁻¹ ▸ ((Inter_in_sets (bin_extension' U₀ U₁)) (extension'_in_sets U₀ U₁ s₀ s₁))

theorem fin_union {M : sigma_algebra X} (S : set (set X)) (fin : finite S) : 
  measurable_collection S → measurable (sUnion S) := 
!induction_on_finite
    (suppose measurable_collection ∅,
     have sUnion ∅ = ∅, from ext (λx, iff.intro
          (suppose x ∈ sUnion ∅,
            obtain c [(hc : c ∈ ∅) (xc : x ∈ c)], from this,
            show _, from !not.elim !not_mem_empty hc)
          (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
     show measurable (sUnion ∅), from this⁻¹ ▸ !sigma_empty) 
    (begin
      intro a s' fins,
      λ s₁, λ s₂, λ s₃,
      (!sUnion_insert)⁻¹ ▸ bin_union a (sUnion s') ((s₃ a) !mem_insert)
      (s₂ (take s, λ t, (s₃ s) (!mem_insert_of_mem t)))
     end) 

theorem fin_inter {M : sigma_algebra X} (S : set (set X)) {fn : finite S} : 
  measurable_collection S → measurable (sInter S) :=
show _, from !induction_on_finite
    (suppose measurable_collection ∅,
     have sInter ∅ = ∅, from ext(λx, iff.intro 
      (suppose x ∈ sInter ∅, 
        have ∀ c, c ∈ ∅ → x ∈ c, from this, 
        have ∀ c, c ∈ ∅ → ¬(x ∈ c), from sorry, -- stuck here --
        show x ∈ ∅, from sorry)
      (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
      show measurable (sInter ∅), from this⁻¹ ▸ !sigma_empty)
     (begin
       intro a s' fins,
       λ s₁, λ s₂, λ H,
         !sInter_insert⁻¹ ▸ (!bin_inter ((H a) !mem_insert) (s₂ ( λ s, λ t, (H s)
         (((λ s, λ t, !mem_of_subset_of_mem (subset_insert a s') t) s) t))))
      end)

theorem measurable_diff_measurable {A B : set X} {M : sigma_algebra X} (Am : measurable A) (Bm : measurable B) :
  measurable (A \ B) := 
have A \ B = A ∩ -B, from !diff_eq,
this ▸ (!bin_inter Am (!sigma_algebra.complements Bm))

lemma measurable_insert_measurable {M : sigma_algebra X} (a : set X) (S : set (set X)) (Hm : measurable_collection (insert a S)) : 
  measurable_collection S := sorry

end sigma_algebra

namespace measure_space

open sigma_algebra

definition disjoint_seq (U : ℕ → set X) : Prop := ∀ i : ℕ, ∀ j : ℕ, i ≠ j → U i ∩ U j = ∅

definition disjoint_fam (S : set (set X)) : Prop := ∀ s, ∀ r, (s ∈ S ∧ r ∈ S) → (s ≠ r → s ∩ r = ∅)

structure measure [class] (M : sigma_algebra X) :=
  (measure : set X → ℝ)
  (measure_empty : measure ∅ = 0)
  (countable_additive : ∀ U : ℕ → set X, disjoint_seq U ∧ (∀ i, measurable (U i)) → (measure (Union U) = (set.Sum (@univ ℕ) (λi, measure (U i)))))

attribute measure.measure [coercion]

-- Need infinite series for all of this --

/- definition fin_measure {X : Type} [M : 𝔐 X] : Prop := μ (space X) < ∞ -/

lemma disjoint_bin_ext {M : sigma_algebra X} (A B : set X) (dsjt : A ∩ B = ∅)  : 
  disjoint_seq (bin_extension A B) := 
take i, take j, suppose neq : i ≠ j,
     show bin_extension A B i ∩ bin_extension A B j = ∅, from 
      decidable.by_cases
        (suppose i ≤ 1,
          decidable.by_cases
            (suppose Hipp : i = 0, 
              have HA : A = bin_extension A B i, from
                begin
                 unfold bin_extension,
                 rewrite [if_pos `i ≤ 1`, if_pos Hipp]
                end,
              decidable.by_cases
                proof 
                  suppose j ≤ 1, 
                  decidable.by_cases
                    (suppose j = 0,
                      show bin_extension A B i ∩ bin_extension A B j = ∅, from !not.elim (`j = 0`⁻¹ ▸ Hipp) neq) 
                    (suppose ¬(j = 0), 
                      have bin_extension A B j = B, from
                       begin
                          unfold bin_extension,
                          rewrite [if_pos `j ≤ 1`, if_neg this]
                       end,
                       show bin_extension A B i ∩ bin_extension A B j = ∅, from this ▸ (HA ▸ dsjt)) 
                  qed
                (suppose ¬(j ≤ 1),  ----
                  have ∅ = bin_extension A B j, from
                    begin
                     unfold bin_extension,
                     rewrite [if_neg this]
                    end,
                  show _, from !inter_empty ▸ ((HA ▸ rfl)⁻¹ ▸ this ▸ rfl)))
            (suppose ¬(i = 0), 
              have bin_extension A B i = B, from 
                begin
                  unfold bin_extension,
                  rewrite [if_pos `i ≤ 1`, if_neg `¬(i = 0)`]
                end,
              decidable.by_cases
                (suppose j ≤ 1, 
                  decidable.by_cases
                    (suppose j = 0, 
                      have bin_extension A B j = A, from
                        begin
                          unfold bin_extension,
                          rewrite [if_pos `j ≤ 1`, if_pos this]
                        end,
                      have bin_extension A B i ∩ bin_extension A B j = A ∩ B, from calc
                           bin_extension A B i ∩ bin_extension A B j = bin_extension A B i ∩ A : `bin_extension A B j = A` ▸ rfl
                                                                 ... = B ∩ A : `bin_extension A B i = B` ▸ this
                                                                 ... = A ∩ B  : !inter.comm ▸ this,
                      show _, from this ▸ dsjt)
                    (suppose ¬(j = 0),
                      have ∀ k, k ≤ 1 ∧ ¬(k = 0) → k = 1, from
                        take k, suppose k ≤ 1 ∧ ¬(k = 0),
                        not_not_elim (not_not_of_not_implies ((iff.elim_right !imp_false) (or.elim (!nat.lt_or_eq_of_le (and.elim_left this))
                          (not.intro( λ H, absurd (!eq_zero_of_le_zero (!le_of_lt_succ H)) (and.elim_right this)))))),
                      have i = j, from (this j (and.intro `j ≤ 1` `¬(j = 0)`))⁻¹ ▸ (this i (and.intro `i ≤ 1` `¬(i = 0)`)),
                      and.elim_left ((iff.elim_right !and_false) (absurd `i = j` neq))))
                (suppose ¬(j ≤ 1),
                      have bin_extension A B j = ∅, from
                        begin
                          unfold bin_extension,
                          rewrite [if_neg `¬(j ≤ 1)`]
                        end,
                      !inter_empty ▸ ((`bin_extension A B i = B` ▸ rfl) ▸ (this ▸ rfl)))))
        (suppose ¬(i ≤ 1), 
          have bin_extension A B i = ∅, from
            begin
              unfold bin_extension,
              rewrite[if_neg `¬(i ≤ 1)`]
            end,
          !empty_inter ▸ (this ▸ rfl))

theorem bin_additive {M : sigma_algebra X} {μ : measure M} (A B : set X) (s₁ : measurable A) (s₂ : measurable B) (dsjt : A ∩ B = ∅) : 
  μ (A ∪ B) = μ A + μ B := 
  have disjoint_seq (bin_extension A B) ∧ (∀ i, measurable (bin_extension A B i)), from and.intro (disjoint_bin_ext A B dsjt) (extension_measurable A B s₁ s₂),
  have H1 : μ (Union (bin_extension A B)) = set.Sum (@univ ℕ) (λi, μ (bin_extension A B i)), from !measure.countable_additive this,
  have H2 : set.Sum (@univ ℕ) (λi, μ (bin_extension A B i)) = μ A + μ B, from sorry, 
  have H3 : Union (bin_extension A B) = A ∪ B, from ext(λx, iff.intro
    (suppose x ∈ Union (bin_extension A B),
       obtain i (Hi : x ∈ bin_extension A B i), from this,
       show _, from 
         decidable.by_cases
           (suppose H1 : i ≤ 1,
             decidable.by_cases
               (suppose i = 0,
                 have bin_extension A B i = A, from 
                   begin
                     unfold bin_extension,
                     rewrite[if_pos H1, if_pos this]
                   end,
                 have x ∈ A, from this ▸ Hi,
                 show x ∈ A ∪ B, from !mem_union_left this)
               (suppose ¬(i = 0), 
                 have bin_extension A B i = B, from 
                   begin
                     unfold bin_extension,
                     rewrite[if_pos H1, if_neg this]
                   end,
                 have x ∈ B, from this ▸ Hi,
                 show x ∈ A ∪ B, from !mem_union_right this))
           (suppose ¬(i ≤ 1),
               have bin_extension A B i = ∅, from 
                 begin
                   unfold bin_extension,
                   rewrite[if_neg this]
                 end,
               have x ∈ ∅, from this ▸ Hi,
               show x ∈ A ∪ B, from !not.elim !not_mem_empty this)) 
       (suppose x ∈ A ∪ B, 
        have HA : x ∈ A → ∃ i, x ∈ bin_extension A B i, from 
          suppose x ∈ A,
          show ∃ i, x ∈ bin_extension A B i, from exists.intro 0 this,
        have HB : x ∈ B → ∃ i, x ∈ bin_extension A B i, from 
          suppose x ∈ B,
          show ∃ i, x ∈ bin_extension A B i, from exists.intro 1 this,
        show x ∈ Union (bin_extension A B), from or.elim this HA HB)),
  show μ (A ∪ B) = μ A + μ B, from H3 ▸ (H1⁻¹ ▸ H2)

lemma Sum_insert_of_not_mem' (f : (set X) → real) {a : set X} {s : set (set X)} (fins : finite s) (H : a ∉ s) :
  set.Sum (insert a s) f = f a + set.Sum s f := algebra.set.Sum_insert_of_not_mem f H

lemma dsjt_insert_dsjt_inter (s : set (set X)) (a : set X) (dsjt : disjoint_fam (insert a s)) (notin : a ∉ s) :
  a ∩ sUnion s = ∅ := 
ext(take x, iff.intro 
  (suppose x ∈ a ∩ sUnion s,
    obtain c [(cs : c ∈ s) (xc : x ∈ c)], from and.elim_right `x ∈ a ∩ sUnion s`,
    have a ≠ c, from not.intro(
      suppose a = c,
      have a ∈ s, from this⁻¹ ▸ cs,
      show false, from notin this),
    have a ∩ c = ∅, from dsjt a c (and.intro !mem_insert (!mem_insert_of_mem cs)) this,
    have x ∈ a ∩ c, from and.intro (and.elim_left `x ∈ a ∩ sUnion s`) xc,
    show x ∈ ∅, from `a ∩ c = ∅` ▸ this)
  (suppose x ∈ ∅, !not.elim !not_mem_empty this))

lemma dsjt_fam_insert_dsjt (s : set (set X)) (a : set X) (dsjt : disjoint_fam (insert a s)) :
  disjoint_fam s := 
take q, take r,
suppose q ∈ s ∧ r ∈ s,
suppose q ≠ r,
have q ∈ insert a s, from !mem_insert_of_mem (and.elim_left `q ∈ s ∧ r ∈ s`),
have r ∈ insert a s, from !mem_insert_of_mem (and.elim_right `q ∈ s ∧ r ∈ s`),
show q ∩ r = ∅, from (dsjt q r) (and.intro `q ∈ insert a s` this) `q ≠ r`

theorem fin_additive {M : sigma_algebra X} {μ : measure M} (S : set (set X)) [fin : finite S] : 
  (measurable_collection S ∧ disjoint_fam S) → μ (sUnion S) = set.Sum S μ :=
!induction_on_finite
  (suppose measurable_collection ∅ ∧ disjoint_fam ∅,
   have (sUnion ∅) = ∅, from ext(take x, iff.intro 
    (suppose x ∈ sUnion ∅,
            obtain c [(hc : c ∈ ∅) (xc : x ∈ c)], from this,
            show _, from !not.elim !not_mem_empty hc)
          (suppose x ∈ ∅, !not.elim !not_mem_empty this)),
   have μ(sUnion ∅) = 0, from (measure.measure_empty M) ▸ (this ▸ rfl),
   have set.Sum ∅ μ = 0, from !set.Sum_empty,
   show μ (sUnion ∅) = set.Sum ∅ μ, from this⁻¹ ▸ `μ(sUnion ∅) = 0`)
  (begin
    intro a s' fins,
    λ s₁, λ s₂, λ s₃,
    (Sum_insert_of_not_mem' μ fins s₁)⁻¹ ▸ ((s₂ (and.intro (!measurable_insert_measurable (and.elim_left s₃)) (dsjt_fam_insert_dsjt s' a
    (and.elim_right s₃)))) ▸ ((!bin_additive (((and.elim_left s₃) a) !mem_insert) (fin_union s' fins (!measurable_insert_measurable (and.elim_left s₃))) 
    (dsjt_insert_dsjt_inter s' a (and.elim_right s₃) s₁))  ▸ (!sUnion_insert ▸ rfl))) 
   end)

theorem measure_mon {M : sigma_algebra X} (μ : measure M) (A B : set X) (s₁ : measurable A) (s₂ : measurable B) (sub : A ⊆ B) :
  μ A ≤ μ B := sorry 

theorem sub_additive {M : sigma_algebra X} {μ : measure M} (S : set (set X)) (Ms : measurable_collection S) : 
  μ (sUnion S) ≤ set.Sum S μ := sorry

end measure_space

end measure

