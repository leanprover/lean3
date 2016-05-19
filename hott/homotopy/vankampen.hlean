/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import hit.pushout algebra.category.constructions.pushout algebra.category.constructions.type
       algebra.category.functor.equivalence

open eq pushout category functor sum iso paths set_quotient is_trunc trunc pi quotient
     is_equiv

namespace pushout
  section
  universe variables u v w
  parameters {TL : Type.{u}} {BL : Type.{v}} {TR : Type.{w}} (f : TL → BL) (g : TL → TR)

  definition pushout_of_sum [unfold 6] (x : BL + TR) : pushout f g :=
  quotient.class_of _ x

  local notation `C` := Groupoid_pushout      (fundamental_groupoid BL) (fundamental_groupoid TR) f g
  local notation `R` := pushout_prehom_index  (fundamental_groupoid BL) (fundamental_groupoid TR) f g
  local notation `Q` := pushout_hom_rel_index (fundamental_groupoid BL) (fundamental_groupoid TR) f g

  protected definition code [unfold 7] (x : BL + TR) (y : pushout f g) : Type.{max u v w} :=
  begin
    refine quotient.elim_type _ _ y,
    { clear y, intro y, exact @hom C _ x y},
    { clear y, intro y z r, induction r with y, fapply equiv_postcompose,
      { apply class_of, exact [pushout_prehom_index.DE _ _ y]},
      { refine all_iso _}}
  end

  definition is_set_code (x : BL + TR) (y : pushout f g) : is_set (code x y) :=
  begin
    induction y using pushout.rec_prop, apply is_set_hom, apply is_set_hom,
  end
  local attribute is_set_code [instance]

  -- encode is easy
  definition encode {x : BL + TR} {y : pushout f g} (p : trunc 0 (pushout_of_sum x = y)) :
    code x y :=
  begin
    induction p with p,
    exact transport (code x) p id
  end

  -- decode is harder
  definition decode_reduction_rule [unfold 8] ⦃x x' : BL + TR⦄ (i : R x x') :
    trunc 0 (pushout_of_sum x = pushout_of_sum x') :=
  begin
    induction i,
    { exact tap inl f_1},
    { exact tap inr g_1},
    { exact tr (glue c)},
    { exact tr (glue c)⁻¹},
  end

  definition decode_list ⦃x x' : BL + TR⦄ (l : paths R x x') :
    trunc 0 (pushout_of_sum x = pushout_of_sum x') :=
  realize (λa a', trunc 0 (pushout_of_sum a = pushout_of_sum a'))
          decode_reduction_rule
          (λa, tidp)
          (λa₁ a₂ a₃, tconcat) l

  definition decode_list_nil (x : BL + TR) : decode_list (@nil _ _ x) = tidp :=
  idp

  definition decode_list_cons ⦃x₁ x₂ x₃ : BL + TR⦄ (r : R x₂ x₃) (l : paths R x₁ x₂) :
    decode_list (r :: l) = tconcat (decode_list l) (decode_reduction_rule r) :=
  idp

  definition decode_list_singleton ⦃x₁ x₂ : BL + TR⦄ (r : R x₁ x₂) :
    decode_list [r] = decode_reduction_rule r :=
  realize_singleton (λa b p, tidp_tcon p) r

  definition decode_list_pair ⦃x₁ x₂ x₃ : BL + TR⦄ (r₂ : R x₂ x₃) (r₁ : R x₁ x₂) :
    decode_list [r₂, r₁] = tconcat (decode_reduction_rule r₁) (decode_reduction_rule r₂) :=
  realize_pair (λa b p, tidp_tcon p) r₂ r₁

  definition decode_list_append ⦃x₁ x₂ x₃ : BL + TR⦄ (l₂ : paths R x₂ x₃)
    (l₁ : paths R x₁ x₂) :
    decode_list (l₂ ++ l₁) = tconcat (decode_list l₁) (decode_list l₂) :=
  realize_append (λa b c d, tassoc) (λa b, tcon_tidp) l₂ l₁

  theorem decode_list_rel ⦃x x' : BL + TR⦄ {l l' : paths R x x'} (H : Q l l') :
    decode_list l = decode_list l' :=
  begin
    induction H,
    { rewrite [decode_list_pair, decode_list_singleton], exact !tap_tcon⁻¹},
    { rewrite [decode_list_pair, decode_list_singleton], exact !tap_tcon⁻¹},
    { rewrite [decode_list_pair, decode_list_nil], exact ap tr !con.right_inv},
    { rewrite [decode_list_pair, decode_list_nil], exact ap tr !con.left_inv},
    { apply decode_list_singleton},
    { apply decode_list_singleton}
  end

  definition decode_point [unfold 8] {x x' : BL + TR} (c : @hom C _ x x') :
    trunc 0 (pushout_of_sum x = pushout_of_sum x') :=
  begin
    induction c with l,
    { exact decode_list l},
    { induction H with H, refine realize_eq _ _ _ H,
      { intros, apply tassoc},
      { intros, apply tcon_tidp},
      { clear H a a', intros, exact decode_list_rel a}}
  end

  theorem decode_coh (x : BL + TR) (y : TL) (p : trunc 0 (pushout_of_sum x = inl (f y))) :
    p =[glue y] tconcat p (tr (glue y)) :=
  begin
    induction p with p,
    apply trunc_pathover, apply eq_pathover_constant_left_id_right,
    apply square_of_eq, exact !idp_con⁻¹
  end

  definition decode [unfold 7] {x : BL + TR} {y : pushout f g} (c : code x y) :
    trunc 0 (pushout_of_sum x = y) :=
  begin
    induction y using quotient.rec with y,
    { exact decode_point c},
    { induction H with y, apply arrow_pathover_left, intro c,
      revert c, apply @set_quotient.rec_prop, { intro z, apply is_trunc_pathover},
      intro l,
      refine _ ⬝op ap decode_point !quotient.elim_type_eq_of_rel⁻¹,
      apply decode_coh}
  end

  -- report the failing of esimp in the commented-out proof below
--   definition decode [unfold 7] {x : BL + TR} {y : pushout f g} (c : code x y) :
--     trunc 0 (pushout_of_sum x = y) :=
--   begin
--     induction y using quotient.rec with y,
--     { exact decode_point c},
--     { induction H with y, apply arrow_pathover_left, intro c,
--       revert c, apply @set_quotient.rec_prop, { intro z, apply is_trunc_pathover},
--       intro l,
--       refine _ ⬝op ap decode_point !quotient.elim_type_eq_of_rel⁻¹,
-- -- REPORT THIS!!! esimp fails here, but works after this change
--   --esimp,
--       change pathover (λ (a : pushout f g), trunc 0 (eq (pushout_of_sum x) a))
--       (decode_point (class_of l))
--       (glue y)
--       (decode_point (class_of ((pushout_prehom_index.lr (fundamental_groupoid_functor f)
--         (fundamental_groupoid_functor g) id) :: l))),
--     esimp, rewrite [▸*, decode_list_cons, ▸*], generalize (decode_list l), clear l,
--     apply @trunc.rec, { intro z, apply is_trunc_pathover},
--     intro p, apply trunc_pathover, apply eq_pathover_constant_left_id_right,
--     apply square_of_eq, exact !idp_con⁻¹}
--   end

  -- decode-encode is easy
  protected theorem decode_encode {x : BL + TR} {y : pushout f g}
    (p : trunc 0 (pushout_of_sum x = y)) : decode (encode p) = p :=
  begin
    induction p with p, induction p, reflexivity
  end

  -- encode-decode is harder
  definition code_comp [unfold 8] {x y : BL + TR} {z : pushout f g}
    (c : code x (pushout_of_sum y)) (d : code y z) : code x z :=
  begin
    induction z using quotient.rec with z,
    { exact d ∘ c},
    { induction H with z,
      apply arrow_pathover_left, intro d,
      refine !pathover_tr ⬝op _,
      refine !elim_type_eq_of_rel ⬝ _ ⬝ ap _ !elim_type_eq_of_rel⁻¹,
      apply assoc}
  end

  theorem encode_tcon' {x y : BL + TR} {z : pushout f g}
    (p : trunc 0 (pushout_of_sum x = pushout_of_sum y))
    (q : trunc 0 (pushout_of_sum y = z)):
    encode (tconcat p q) = code_comp (encode p) (encode q) :=
  begin
    induction q with q,
    induction q,
    refine ap encode !tcon_tidp ⬝ _,
    symmetry, apply id_left
  end

  theorem encode_tcon {x y z : BL + TR}
    (p : trunc 0 (pushout_of_sum x = pushout_of_sum y))
    (q : trunc 0 (pushout_of_sum y = pushout_of_sum z)):
    encode (tconcat p q) = encode q ∘ encode p :=
  encode_tcon' p q

  open category.pushout_hom_rel_index

  theorem encode_decode_singleton {x y : BL + TR} (r : R x y) :
    encode (decode_reduction_rule r) = class_of [r] :=
  begin
    have is_prop (encode (decode_reduction_rule r) = class_of [r]), from !is_trunc_eq,
    induction r,
    { induction f_1 with p, induction p, symmetry, apply eq_of_rel,
      apply tr, apply paths_rel_of_Q, apply idD},
    { induction g_1 with p, induction p, symmetry, apply eq_of_rel,
      apply tr, apply paths_rel_of_Q, apply idE},
    { refine !elim_type_eq_of_rel ⬝ _, apply eq_of_rel, apply tr, rewrite [append_nil]},
    { refine !elim_type_eq_of_rel_inv' ⬝ _, apply eq_of_rel, apply tr, rewrite [append_nil]}
  end

  local attribute pushout [reducible]
  protected theorem encode_decode {x : BL + TR} {y : pushout f g} (c : code x y) :
    encode (decode c) = c :=
  begin
    induction y using quotient.rec_prop with y,
    revert c, apply @set_quotient.rec_prop, { intro, apply is_trunc_eq}, intro l,
    change encode (decode_list l) = class_of l,
    -- do induction on l
    induction l,
    { reflexivity},
    { rewrite [decode_list_cons, encode_tcon, encode_decode_singleton, v_0]}
  end

  definition pushout_teq_equiv [constructor] (x : BL + TR) (y : pushout f g) :
    trunc 0 (pushout_of_sum x = y) ≃ code x y :=
  equiv.MK encode
           decode
           encode_decode
           decode_encode

  definition vankampen [constructor] (x y : BL + TR) :
    trunc 0 (pushout_of_sum x = pushout_of_sum y) ≃ @hom C _ x y :=
  pushout_teq_equiv x (pushout_of_sum y)

  definition decode_point_comp [unfold 8] {x₁ x₂ x₃ : BL + TR}
    (c₂ : @hom C _ x₂ x₃) (c₁ : @hom C _ x₁ x₂) :
    decode_point (c₂ ∘ c₁) = tconcat (decode_point c₁) (decode_point c₂) :=
  begin
    induction c₂ using set_quotient.rec_prop with l₂,
    induction c₁ using set_quotient.rec_prop with l₁,
    apply decode_list_append
  end

  definition vankampen_functor [constructor] : C ⇒ fundamental_groupoid (pushout f g) :=
  begin
    fconstructor,
    { exact pushout_of_sum},
    { intro x y c, exact decode_point c},
    { intro x, reflexivity},
    { intro x y z d c, apply decode_point_comp}
  end

  definition fully_faithful_vankampen_functor : fully_faithful vankampen_functor :=
  begin
    intro x x',
    fapply adjointify,
    { apply encode},
    { intro p, apply decode_encode},
    { intro c, apply encode_decode}
  end

  definition essentially_surjective_vankampen_functor : essentially_surjective vankampen_functor :=
  begin
    intro z, induction z using quotient.rec_prop with x,
    apply exists.intro x, reflexivity
  end

  definition is_weak_equivalence_vankampen_functor [constructor] :
    is_weak_equivalence vankampen_functor :=
  begin
    constructor,
    { exact fully_faithful_vankampen_functor},
    { exact essentially_surjective_vankampen_functor}
  end

  end
end pushout
