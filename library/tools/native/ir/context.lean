import tools.native.ir.syntax

namespace native.ir

meta structure context :=
  (items : rb_map name ir.item)

meta def new_context
(decls : list ir.decl)
(defns : list ir.defn)
(types : list ir.type_decl) : context := do
  let items := list.map (ir.item.defn) defns ++ list.map (ir.item.decl) decls,
  let named_items := list.map (fun i, (ir.item.get_name i, i)) $ items,
  context.mk $ rb_map.of_list named_items

meta def lookup_item (n : name) (ctxt : context) : option ir.item :=
  rb_map.find (context.items ctxt) n

meta def context.extend_items : rb_map name ir.item → list (name × ir.item) → rb_map name ir.item
| items [] := items
| items ((n, i) :: bs) :=
  context.extend_items (items^.insert n i) bs

meta def context.extend (ctx : context) (new_items : list (name × ir.item)) : context :=
  match ctx with
  | ⟨ items ⟩ := ⟨ context.extend_items items new_items ⟩
  end

meta def context.to_items (ctx : context) : list ir.item :=
  list.map prod.snd $ ctx^.items^.to_list

end native.ir
