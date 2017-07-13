@[user_attribute] def ir_def : user_attribute := {
  name := `ir_def,
  descr := "makes the IR definition availible to the native compiler"
}

@[user_attribute] def ir_decl : user_attribute := {
  name := `ir_decl,
  descr := "makes the IR declaration availible to the native compiler"
}

@[user_attribute] def ir_type : user_attribute := {
  name := `ir_type,
  descr := "makes the IR type declaration availible to the native compiler"
}

@[user_attribute] def backend.attr : user_attribute := {
  name := `backend,
  descr := "registers the backend with the native compiler"
}

open tactic

meta def make_list (type : expr) : list expr → tactic expr
| [] := mk_mapp `list.nil [some type]
| (e :: es) := do
  tail ← make_list es,
  mk_mapp `list.cons [some type, some e, some tail]

meta def get_attribute_body (attr : name) (type : expr) : tactic expr := do
  decl ← get_decl attr,
  match decl with
  | (declaration.defn _ _ ty body _ _) :=
    if (not $ ty = type)
    then fail $ "expected a declaration with attribute `" ++ attr.to_string ++ "to have the type `" ++ type.to_string ++ "`"
    else pure body
  | _ := fail $ "the `" ++ attr.to_string ++ "` can only be attached to definitions"
  end

meta def get_attribute_bodies (attr : name) (type : expr) : tactic expr := do
  names ← attribute.get_instances attr,
  bodies ← monad.for names (fun n, get_attribute_body n type),
  make_list type bodies

meta def get_ir_decls : tactic expr := do
  ty ← mk_const `ir.decl,
  get_attribute_bodies `ir_decl ty

meta def get_ir_defns : tactic expr := do
  ty ← mk_const `ir.defn,
  get_attribute_bodies `ir_def ty

meta def get_ir_types : tactic expr := do
  ty ← mk_const `ir.type_decl,
  get_attribute_bodies `ir_type ty

meta def get_backends : tactic expr := do
  ty ← mk_const `native.backend,
  get_attribute_bodies `backend ty
