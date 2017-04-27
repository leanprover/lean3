prelude

import init.data.option.basic
import init.meta.declaration
import init.meta.tactic
import init.meta.attribute

meta constant pos_info_provider : Type
-- this returns none most of the time, how do we make this work?
meta constant pos_info_provider.expr_pos : pos_info_provider → expr → option pos

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

-- A lint for deprecated APIs.
run_cmd mk_name_set_attr `deprecated

meta def expr_contains_deprecated (pos_prov : pos_info_provider) (is_deprecated : name → bool) : expr → option pos
| (expr.const n ls) :=
if is_deprecated n
then trace "hellO" (pos_prov.expr_pos (expr.const n ls))
else none
| _ := none

meta def mk_is_deprecated : tactic (name → bool) :=
do nset ← get_name_set_for_attr `deprecated,
   return $ name_set.contains nset

private meta def warn_deprecated (pos_prov : pos_info_provider) : declaration → tactic unit
| (declaration.ax _ _ _) := return ()
| (declaration.cnst _ _ _ _) := return ()
| (declaration.defn _ _ ty body _ _) :=
do is_dep ← mk_is_deprecated,
   set ← get_name_set_for_attr `deprecated,
   match expr_contains_deprecated pos_prov is_dep body with
   | none := return ()
   | some pos := save_info_thunk pos (fun u, to_fmt "hereee")
   end
| (declaration.thm _ _ _ _) := return ()

@[linter] private meta def deprecated_linter : linter :=
⟨ warn_deprecated ⟩
