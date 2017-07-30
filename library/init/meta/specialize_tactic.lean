prelude

import init.meta.tactic
import init.meta.interactive_base
import init.meta.interactive

namespace tactic
namespace interactive

open interactive interactive.types expr

meta def specialize_core (loc : expr) (args : list expr) : tactic unit :=
do let original_name := loc.local_pp_name,
   new_name ← mk_fresh_name,
   rename original_name new_name,
   F ← get_local new_name,
   note original_name none (expr.mk_app F args),
   clear_lst [new_name],
   pure ()

meta def specialize (e : parse texpr) : tactic unit := do
  e' ← i_to_expr e,
  let fn := expr.get_app_fn e',
  let args :=  expr.get_app_args e',
  if expr.is_local_constant fn
  then specialize_core fn args
  else tactic.fail "specialize requires a term of the form (H x_1 .. x_n) where H appears in the local context"

end interactive
end tactic
