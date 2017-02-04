import .ir

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

record builder_state :=
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

-- @[class] structure compute_arity (A : Type) :=
--   (arity : nat)

-- -- @[priority std.priority.default-10] instance fall_thru {A : Type} : compute_arity A :=
-- --    (| _, 0 |)
-- @[priority std.priority.default+10] instance arrow {A B : Type} {n : nat} [b_arity : compute_arity B] : compute_arity (A → B) :=
--   (| _, @compute_arity.arity _ b_arity + 1 |)

-- def mk_defn {F : Type} [f_arity : compute_arity F] (f : F) : nat :=
--   @compute_arity.arity _ f_arity

-- def foo : nat :=
--   @mk_defn _ _ (fun (x y z : unit), ())

-- vm_eval foo
