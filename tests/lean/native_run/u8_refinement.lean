import data.bitvec
import data.list
import system.io
import tools.native

set_option debugger true

@[reducible] def u8 : Type := bitvec 8

def u8.add : u8 → u8 → u8 := bitvec.add

def u8.put : u8 → io unit :=
  fun u, put_str_ln u

@[ir_def] def u8.ir.add : ir.defn :=
  ir.defn.mk `u8.add [(`a, ir.ty.object none), (`b, ir.ty.object none)] (ir.ty.object none) $ (
    ir.stmt.seq [
      ir.stmt.e $ ir.expr.panic "need to implement u8.add"
    ])

@[ir_def] def u8.ir.put : ir.defn :=
  ir.defn.mk `u8.put [(`n, ir.ty.object none)] (ir.ty.object none) ir.stmt.nop

@[breakpoint] def main : io unit :=
  u8.put $ (u8.add 0 1)
