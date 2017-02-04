prelude

import init.meta.rb_map
import tools.native.ir.ir

namespace native.ir

meta record context :=
  (items : rb_map name ir.item)

meta def new_context
(decls : list ir.decl)
(defns : list ir.defn)
(types : list ir.type_decl) : context := do
  let items := list.map (ir.item.defn) defns ++ list.map (ir.item.decl) decls,
  named_items := list.map (fun i, (ir.item.get_name i, i)) $ items in
  context.mk $ rb_map.of_list named_items

meta def lookup_item (n : name) (ctxt : context) : option ir.item :=
  rb_map.find (context.items ctxt) n

end native.ir
