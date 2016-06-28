/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import hit.pushout hit.prop_trunc algebra.category.constructions.pushout
       algebra.category.constructions.fundamental_groupoid algebra.category.functor.equivalence

open eq pushout category functor sum iso paths set_quotient is_trunc trunc pi quotient
     is_equiv fiber equiv function

namespace pushout
  section
  universe variables u v w
  parameters {S TL : Type.{u}} -- do we want to put these in different universe levels?
             {BL : Type.{v}} {TR : Type.{w}} (k : S → TL) (f : TL → BL) (g : TL → TR)
             [ksurj : is_surjective k]

  definition pushout_of_sum [unfold 6] (x : BL + TR) : pushout f g :=
  quotient.class_of _ x

  include ksurj

  local notation `F` := Π₁⇒ f
  local notation `G` := Π₁⇒ g
  local notation `C` := Groupoid_bpushout k F G
  local notation `R` := bpushout_prehom_index k F G
  local notation `Q` := bpushout_hom_rel_index k F G
  local attribute is_trunc_equiv [instance]

  open category.bpushout_prehom_index category.bpushout_hom_rel_index paths.paths_rel
  protected definition code_equiv_pt (x : BL + TR) {y : TL} {s : S} (p : k s = y) :
    @hom C _ x (sum.inl (f y)) ≃ @hom C _ x (sum.inr (g y)) :=
  begin
    fapply equiv_postcompose,
    { apply class_of,
      refine [iE k F G (tap g (tr p)), DE k F G s, iD k F G (tap f (tr p⁻¹))]},
    refine all_iso _
  end

  protected definition code_equiv_pt_constant (x : BL + TR) {y : TL} {s s' : S}
    (p : k s = y) (p' : k s' = y) : code_equiv_pt x p = code_equiv_pt x p' :=
  begin
    apply equiv_eq, intro g,
    apply ap (λx, x ∘ _),
    induction p',
    refine eq_of_rel (tr _) ⬝ (eq_of_rel (tr _))⁻¹,
    { exact [DE k _ _ s']},
    { refine rtrans (rel [_] (cohDE F G (tr p))) _,
      refine rtrans (rcons _ (rel [] !DD)) _,
      refine tr_rev (λx, paths_rel _ [_ , iD k F G (tr x)] _)
                    (!ap_con⁻¹ ⬝ ap02 f !con.left_inv) _,
      exact rcons _ (rel [] !idD)},
    refine rtrans (rel _ !idE) _,
    exact rcons _ (rel [] !idD)
  end

  protected definition code_equiv (x : BL + TR) (y : TL) :
    @hom C _ x (sum.inl (f y)) ≃ @hom C _ x (sum.inr (g y)) :=
  begin
    refine @is_prop.elim_set _ _ _ _ _ (ksurj y), { apply @is_trunc_equiv: apply is_set_hom},
    { intro v, cases v with s p,
      exact code_equiv_pt x p},
    intro v v', cases v with s p, cases v' with s' p',
    exact code_equiv_pt_constant x p p'
  end

  theorem code_equiv_eq (x : BL + TR) (s : S) :
    code_equiv x (k s) = @(equiv_postcompose (class_of [DE k F G s])) !all_iso :=
  begin
    apply equiv_eq, intro h,
--    induction h using set_quotient.rec_prop with l,
    refine @set_quotient.rec_prop _ _ _ _ _ h, {intro l, apply is_trunc_eq, apply is_set_hom},
    intro l,
    have ksurj (k s) = tr (fiber.mk s idp), from !is_prop.elim,
    refine ap (λz, to_fun (@is_prop.elim_set _ _ _ _ _ z) (class_of l)) this ⬝ _,
    change class_of ([iE k F G (tr idp), DE k F G s, iD k F G (tr idp)] ++ l) =
           class_of (DE k F G s :: l) :> @hom C _ _ _,
    refine eq_of_rel (tr _) ⬝ (eq_of_rel (tr _)),
    { exact DE k F G s :: iD k F G (tr idp) :: l},
    { change paths_rel Q ([iE k F G (tr idp)] ++ (DE k F G s :: iD k F G (tr idp) :: l))
                         (nil ++ (DE k F G s :: iD k F G (tr idp) :: l)),
      apply rel ([DE k F G s, iD k F G (tr idp)] ++ l),
      apply idE},
    { apply rcons, rewrite [-nil_append l at {2}, -singleton_append], apply rel l, apply idD}
  end

  theorem to_fun_code_equiv (x : BL + TR) (s : S) (h : @hom C _ x (sum.inl (f (k s)))) :
    (to_fun (code_equiv x (k s)) h) = @comp C _ _ _ _ (class_of [DE k F G s]) h :=
  ap010 to_fun !code_equiv_eq h

  protected definition code [unfold 10] (x : BL + TR) (y : pushout f g) : Type.{max u v w} :=
  begin
    refine quotient.elim_type _ _ y,
    { clear y, intro y, exact @hom C _ x y},
    clear y, intro y z r, induction r with y,
    exact code_equiv x y
  end

/-
[iE (ap g p), DE s, iD (ap f p⁻¹)]
-->
[DE s', iD (ap f p), iD (ap f p⁻¹)]
-->
[DE s', iD (ap f p ∘ ap f p⁻¹)]
-->
[DE s']
<--
[iE 1, DE s', iD 1]
-/

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
  definition decode_reduction_rule [unfold 11] ⦃x x' : BL + TR⦄ (i : R x x') :
    trunc 0 (pushout_of_sum x = pushout_of_sum x') :=
  begin
    induction i,
    { exact tap inl f_1},
    { exact tap inr g_1},
    { exact tr (glue (k s))},
    { exact tr (glue (k s))⁻¹},
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
    { apply decode_list_singleton},
    { rewrite [+decode_list_pair], induction h with p, apply ap tr, rewrite [-+ap_compose'],
      exact !ap_con_eq_con_ap⁻¹},
    { rewrite [+decode_list_pair], induction h with p, apply ap tr, rewrite [-+ap_compose'],
      apply ap_con_eq_con_ap}
  end

  definition decode_point [unfold 11] {x x' : BL + TR} (c : @hom C _ x x') :
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
      change pathover (λ a, trunc 0 (eq (pushout_of_sum x) a))
    (decode_list l)
    (eq_of_rel (pushout_rel f g) (pushout_rel.Rmk f g y))
    (decode_point
       (code_equiv x y (class_of l))),
      note z := ksurj y, revert z,
      apply @image.rec, { intro, apply is_trunc_pathover},
      intro s p, induction p, rewrite to_fun_code_equiv,
      refine _ ⬝op (decode_list_cons (DE k F G s) l)⁻¹,
      esimp, generalize decode_list l,
      apply @trunc.rec, { intro p, apply is_trunc_pathover},
      intro p, apply trunc_pathover, apply eq_pathover_constant_left_id_right,
      apply square_of_eq, exact !idp_con⁻¹}
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
--       (decode_point (class_of ((pushout_prehom_index.lr F G id) :: l))),
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

  definition is_surjective.rec {A B : Type} {f : A → B} (Hf : is_surjective f)
    {P : B → Type} [Πb, is_prop (P b)] (H : Πa, P (f a)) (b : B) : P b :=
  by induction Hf b; exact p ▸ H a

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
      note q := ksurj z, revert q, apply @image.rec, { intro, apply is_trunc_eq, apply is_set_code},
      intro s p, induction p,
      refine !to_fun_code_equiv ⬝ _ ⬝ ap (λh, h ∘ c) !to_fun_code_equiv⁻¹, apply assoc}
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

  open category.bpushout_hom_rel_index
  theorem encode_decode_singleton {x y : BL + TR} (r : R x y) :
    encode (decode_reduction_rule r) = class_of [r] :=
  begin
    have is_prop (encode (decode_reduction_rule r) = class_of [r]), from !is_trunc_eq,
    induction r,
    { induction f_1 with p, induction p, symmetry, apply eq_of_rel,
      apply tr, apply paths_rel_of_Q, apply idD},
    { induction g_1 with p, induction p, symmetry, apply eq_of_rel,
      apply tr, apply paths_rel_of_Q, apply idE},
    { refine !elim_type_eq_of_rel ⬝ _, apply to_fun_code_equiv},
    { refine !elim_type_eq_of_rel_inv' ⬝ _, apply ap010 to_inv !code_equiv_eq}
  end

  local attribute pushout [reducible]
  protected theorem encode_decode {x : BL + TR} {y : pushout f g} (c : code x y) :
    encode (decode c) = c :=
  begin
    induction y using quotient.rec_prop with y,
    revert c, apply @set_quotient.rec_prop, { intro, apply is_trunc_eq}, intro l,
    change encode (decode_list l) = class_of l,
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

--Groupoid_pushout k F G

  definition decode_point_comp [unfold 8] {x₁ x₂ x₃ : BL + TR}
    (c₂ : @hom C _ x₂ x₃) (c₁ : @hom C _ x₁ x₂) :
    decode_point (c₂ ∘ c₁) = tconcat (decode_point c₁) (decode_point c₂) :=
  begin
    induction c₂ using set_quotient.rec_prop with l₂,
    induction c₁ using set_quotient.rec_prop with l₁,
    apply decode_list_append
  end

  definition vankampen_functor [constructor] : C ⇒ Π₁ (pushout f g) :=
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

  definition fundamental_groupoid_bpushout [constructor] :
    Groupoid_bpushout k (Π₁⇒ f) (Π₁⇒ g) ≃w Π₁ (pushout f g) :=
  weak_equivalence.mk vankampen_functor is_weak_equivalence_vankampen_functor

  end

  definition fundamental_groupoid_pushout [constructor] {TL BL TR : Type}
    (f : TL → BL) (g : TL → TR) : Groupoid_bpushout (@id TL) (Π₁⇒ f) (Π₁⇒ g) ≃w Π₁ (pushout f g) :=
  fundamental_groupoid_bpushout (@id TL) f g

end pushout
