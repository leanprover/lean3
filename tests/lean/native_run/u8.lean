import init.native.ir

constant u8 : Type

constant u8.add : u8 → u8 → u8
constant u8.of_nat : nat → u8

@[ir_decl] def u8.ir.add : ir.decl :=
  ir.decl.mk `u8.add [(`a, ir.ty.object none), (`b, ir.ty.object none)] (ir.ty.object none)

@[ir_defn] def u8.ir.of_nat : ir.defn :=
  ir.defn.mk `u8.of_nat [(`n, ir.ty.object none)] (ir.ty.object none) ir.stmt.nop

noncomputable instance : has_coe nat u8 :=
  ⟨ u8.of_nat ⟩

noncomputable def main :=
  u8.add (0 : nat) (1 : nat)

