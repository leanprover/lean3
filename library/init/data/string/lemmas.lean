/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.meta

namespace string
lemma empty_ne_str (c : char) (s : string) : empty ≠ str s c :=
begin cases s, unfold str empty, intro h, injection h, contradiction end

lemma str_ne_empty (c : char) (s : string) : str s c ≠ empty :=
begin cases s, unfold str empty, intro h, injection h, contradiction end

lemma str_ne_str_left {c₁ c₂ : char} (s₁ s₂ : string) : c₁ ≠ c₂ → str s₁ c₁ ≠ str s₂ c₂ :=
begin cases s₁, cases s₂, intros h₁ h₂, unfold str at h₂, injection h₂, injection h, contradiction end

lemma str_ne_str_right (c₁ c₂ : char) {s₁ s₂ : string} : s₁ ≠ s₂ → str s₁ c₁ ≠ str s₂ c₂ :=
begin cases s₁, cases s₂, intros h₁ h₂, unfold str at h₂, injection h₂, injection h, subst data, contradiction end

-- lemma replace_char_with_self_is_id :
-- ∀ str c, string.replace_char c (string.str "" c) str = str :=
-- begin
--     intros,
--     cases str,
--     dsimp [replace_char],
--     apply congr,
--     reflexivity,
--     revert c,
--     induction data; intros,
--     case list.nil {
--         simp [to_list],
--         simp [list.reverse, list.reverse_core],
--         admit
--     },
--     case list.cons { admit },
-- end

-- TODO add lemma for split
end string
