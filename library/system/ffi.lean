import system.IO
import init.coe

namespace ffi

-- Be careful when changing this, there is a corresponding enum in `vm_ptr.cpp` which
-- corresponds to the contructor numbering here.
inductive base_type :=
| int
| char

inductive type :=
| base : base_type → type
| array : nat -> type → type
-- | sigma : (nat → type) → type
| void : type


definition base_type_coe [instance] : has_coe base_type type :=
  has_coe.mk (fun bt, type.base bt)

definition cstring : type :=
  type.array 256 (type.base base_type.char)

attribute [reducible] cstring

  -- type.sigma (fun n, type.array n (type.base (base_type.char)))

constant ptr : type -> Type.{1}

definition destructor (T : type) :=
  ptr T -> IO unit

constant base_size_of (T : base_type) : nat

open type

definition sizeof : type -> nat
| sizeof (base bt) := base_size_of bt
| sizeof (array n t) := n * sizeof t
| sizeof void := 0

constant allocate (T : type) (n : nat) : sizeof T = n -> (destructor T) -> IO (ptr T)

constant write_array {n : nat} {T : type} (arr : ptr (array n T)) (i : nat) (value : ptr T) : IO unit
constant read_array {n : nat} {T : type} (arr : ptr (array n T)) (i : nat) : IO (ptr T)

definition new (T : type) : IO (ptr T) :=
  allocate T (sizeof T) rfl (fun x, return unit.star)

-- open base_type
open type

definition value_of : type → Type.{1}
| value_of void := unit
| value_of T := ptr T

attribute [reducible] value_of

-- A special marker for converting 
definition extern (ret : type) (s : string) : list type -> Type.{1}
| extern [] := IO (value_of ret)
| extern (t :: ts) := (value_of t) -> extern ts

attribute [reducible] extern

-- We really need good support for Z's would be nice to define a set of system types.
constant write_nat_as_int : nat -> ptr base_type.int -> IO unit
constant read_int_as_nat : ptr base_type.int -> IO nat
constant write_char_as_char : char -> ptr base_type.char -> IO unit
constant read_char_as_char : ptr base_type.char  -> IO char

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
