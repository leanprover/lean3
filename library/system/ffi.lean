import system.IO
import init.coe

namespace ffi

inductive base_type :=
| int
| char

inductive type :=
| base : base_type → type
| array : nat -> type → type
| sigma : (nat → type) → type
| void : type

definition base_type_coe [instance] : has_coe base_type type :=
  has_coe.mk (fun bt, type.base bt)

definition cstring : type :=
  type.sigma (fun n, type.array n (type.base (base_type.char)))

constant ptr : type -> Type.{1}

definition destructor (T : type) :=
  ptr T -> IO unit

constant base_size_of (T : base_type) : nat

definition sizeof (T : type) : nat := 4

constant allocate (T : type) (n : nat) : sizeof T = n -> (destructor T) -> IO (ptr T)

definition new (T : type) : IO (ptr T) :=
  allocate T (sizeof T) rfl (fun x, return unit.star)

open base_type
open type

definition value_of : type → Type.{1}
| value_of void := unit
| value_of T := ptr T

-- A special marker for converting 
definition extern (ret : type) (s : string) : list type -> Type.{1}
| extern [] := IO (value_of ret)
| extern (t :: ts) := (value_of ret) -> extern ts

constant print_int : extern void "print_int" [int]
attribute [extern] print_int

-- constant extern_open : extern_fn "open" [string, int] int
-- attribute [extern] extern_open

-- constant extern_read : extern_fn "read" [int, int, int] int
-- attribute [extern] extern_read

-- definition upcast [reducible] (t : type) : type :=
--   match t with
--   | type.array _ char := cstring
--   | _ := t
--   end

-- constant upcast_value {T : type} : ptr T = ptr (upcast T)

-- ptr cstring -> (ptr char -> A) -> B

-- definition to_cstring (s : string) : IO (ptr cstring) := do
--   str <- new (array (list.length s) base_type.char),
--   forM (enumerate str) $ do
--     write i c ptr

  -- return (upcast_value str)

-- definition extern_fn_type (ret : type) : list type -> Type
-- | extern_fn_type [] := IO (ptr ret)
-- | extern_fn_type (arg :: args) := ptr arg -> extern_fn_type args

-- constant call {s : string} {ts : list type} {ret : type} : extern_fn s ts ret → extern_fn_type ret ts

-- definition read_file (s : string) : IO string := do
--   fname <- to_cstring s,
--   call extern_read_file fname,
--   return "foo"

-- definition main := do
--   fd <- call open_file 


end ffi

-- allocate (sizeof type.int) type.int rfl

-- constant Extern : Type -> Type -> Type

-- constant open_file : Extern type.int (type.string, type.int)

-- constant
