import system.IO

namespace ffi

inductive type :=
| int
| string

constant ptr : type -> Type

definition destructor (T : type) :=
  ptr T -> IO unit

definition sizeof (T : type) : nat := 4

constant allocate (T : type) (n : nat) : sizeof T = n -> (destructor T) -> IO (ptr T)

end ffi

-- allocate (sizeof type.int) type.int rfl

-- constant Extern : Type -> Type -> Type

-- constant open_file : Extern type.int (type.string, type.int)

-- constant
