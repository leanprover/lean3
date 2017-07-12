import .syntax

open ir

def mk_equals (e1 e2 : ir.expr) : ir.expr :=
  expr.binary_operator op.equals e1 e2

def mk_not_equals (e1 e2 : ir.expr) : ir.expr :=
  expr.binary_operator op.not_equals e1 e2

def mk_add (e1 e2 : ir.expr) : ir.expr :=
  expr.binary_operator op.sub e1 e2

def mk_sub (e1 e2 : ir.expr) : ir.expr :=
  expr.binary_operator op.sub e1 e2

def mk_mul (e1 e2 : ir.expr) : ir.expr :=
  expr.binary_operator op.mul e1 e2

def mk_div (e1 e2 : ir.expr) : ir.expr :=
   expr.binary_operator op.div e1 e2

def mk_int (i : int) : ir.expr :=
  expr.lit $ ir.literal.integer i

structure builder_state :=
  (counter : nat)
  (bindings : list (symbol × ir.ty × ir.expr))

def builder_state.initial :=
  builder_state.mk 0 []

@[reducible] def builder (A : Type) :=
  state builder_state A

def build (action : builder ir.stmt) : ir.stmt :=
  let (stmt, (| _, bs |)) := action builder_state.initial
  in stmt

def letb (sym : ir.symbol) (ty : ir.ty) (body : ir.expr) : builder unit := do
  (| count, bs |) <- state.read,
  state.write (builder_state.mk  count ((sym, ty, body) :: bs))
