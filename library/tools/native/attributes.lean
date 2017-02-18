import init.meta.tactic
import init.meta.constructor_tactic
import init.meta.attribute

definition ir_def : user_attribute := {
  name := `ir_def,
  descr := "makes the IR definition availible to the native compiler"
}

definition ir_decl : user_attribute := {
  name := `ir_decl,
  descr := "makes the IR declaration availible to the native compiler"
}

definition ir_type : user_attribute := {
  name := `ir_type,
  descr := "makes the IR type declaration availible to the native compiler"
}

definition compiler_plugin : user_attribute := {
  name := `compiler_plugin,
  descr := "registers the compiler plugin for use in the native compiler"
}

def backend : user_attribute := {
  name := `backend,
  descr := "registers the backend with the native compiler"
}

run_command attribute.register `ir_def
run_command attribute.register `ir_decl
run_command attribute.register `ir_type
run_command attribute.register `compiler_plugin
run_command attribute.register `backend
