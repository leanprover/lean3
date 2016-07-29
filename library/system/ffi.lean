import system.IO

namespace ffi

inductive base_type :=
| int
| 
inductive type :=
| int
| string

constant ptr : type -> Type

definition destructor (T : type) :=
  ptr T -> IO unit

definition sizeof (T : type) : nat := 4

constant allocate (T : type) (n : nat) : sizeof T = n -> (destructor T) -> IO (ptr T)

open type

constant extern_fn (ts : list type) : type -> Type

constant open_file : extern_fn [string, int] int
attribute [extern] open_file

constant read_file : extern_fn [int, int, int] int
attribute [extern] read_file

constant call {ts : list type} {ret : type} : extern_fn ts ret -> IO (ptr ret)

definition main := do
  fd <- call open_file


end ffi

-- allocate (sizeof type.int) type.int rfl

-- constant Extern : Type -> Type -> Type

-- constant open_file : Extern type.int (type.string, type.int)

-- constant
