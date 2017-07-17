import tools.native.backends.cpp
import tools.native.ir.syntax
import system.io

variable [io.interface]

meta def main : io unit :=
io.put_str $ to_string $ format_cpp.stmt (ir.stmt.letb `f ir.base_type.int ir.expr.uninitialized ir.stmt.nop)

#eval main
