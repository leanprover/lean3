def ir_def : user_attribute := {
  name := `ir_def,
  descr := "makes the IR definition availible to the native compiler"
}

def ir_decl : user_attribute := {
  name := `ir_decl,
  descr := "makes the IR declaration availible to the native compiler"
}

def ir_type : user_attribute := {
  name := `ir_type,
  descr := "makes the IR type declaration availible to the native compiler"
}

def compiler_plugin : user_attribute := {
  name := `compiler_plugin,
  descr := "registers the compiler plugin for use in the native compiler"
}

def backend : user_attribute := {
  name := `backend,
  descr := "registers the backend with the native compiler"
}

run_cmd attribute.register `ir_def
run_cmd attribute.register `ir_decl
run_cmd attribute.register `ir_type
run_cmd attribute.register `compiler_plugin
run_cmd attribute.register `backend
