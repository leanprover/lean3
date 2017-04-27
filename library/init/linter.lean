prelude

import init.data.option.basic
import init.meta.declaration
import init.meta.tactic

meta constant pos_info_provider : Type
meta constant pos_info_provider.expr_pos : pos_info_provider → option pos

meta structure linter :=
(lint : pos_info_provider → declaration → tactic unit)

open tactic

meta def linter.get_decl_pos (d : declaration) : tactic pos :=
do env ← get_env,
   match env.decl_pos d.to_name with
   | none := failed
   | some pos := return pos
   end

-- A lint for warning about declaration naming conventions.
private def name_str_is_accepted_style (s : string) : bool :=
if (64 < s.head.to_nat) && (s.head.to_nat < 91)
then bool.ff
else bool.tt

private def name_is_accepted_style : name → bool
| (name.mk_numeral i n) := name_is_accepted_style n
| (name.mk_string str n) := name_str_is_accepted_style str.reverse &&
                            name_is_accepted_style n
| (name.anonymous) := bool.tt

private meta def warn_decl_name (pos_prov : pos_info_provider) (decl : declaration) : tactic unit :=
let name := decl.to_name in
if name_is_accepted_style name
then do pos ← linter.get_decl_pos decl, save_info_thunk pos (fun u, to_fmt $ "foooo bar")
else trace $ "warning: `" ++ to_string name ++ "` violates style guidelines"

@[linter] private meta def warn_decl_names : linter :=
⟨ warn_decl_name ⟩
