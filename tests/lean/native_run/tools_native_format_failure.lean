import tools.native.format
import system.io

meta def main : io unit :=
    put_str $ to_string $ format_cpp.stmt (ir.stmt.letb `f ir.ty.int ir.expr.uninitialized ir.stmt.nop)

vm_eval main
