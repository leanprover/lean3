/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
-/

import ..groupoid ..functor.basic

open eq is_trunc iso trunc functor

namespace category

  definition fundamental_precategory [constructor] (A : Type) : Precategory :=
  precategory.MK A
                 (λa a', trunc 0 (a = a'))
                 _
                 (λa₁ a₂ a₃ q p, tconcat p q)
                 (λa, tidp)
                 (λa₁ a₂ a₃ a₄ r q p, tassoc p q r)
                 (λa₁ a₂, tcon_tidp)
                 (λa₁ a₂, tidp_tcon)

  definition fundamental_groupoid [constructor] (A : Type) : Groupoid :=
  groupoid.MK (fundamental_precategory A)
              (λa b p, is_iso.mk (tinverse p) (right_tinv p) (left_tinv p))

  definition fundamental_groupoid_functor [constructor] {A B : Type} (f : A → B) :
    fundamental_groupoid A ⇒ fundamental_groupoid B :=
  functor.mk f (λa a', tap f) (λa, tap_tidp f) (λa₁ a₂ a₃ q p, tap_tcon f p q)

  notation `Π₁` := fundamental_groupoid

  notation `Π₁⇒` := fundamental_groupoid_functor

end category
