import system.IO
import system.result
import init.coe

namespace ffi

-- Be careful when changing this, there is a corresponding enum in `vm_ptr.cpp` which
-- corresponds to the contructor numbering here.
inductive base_type
| int
| char

inductive type
-- A base type with sizing and alignment corresponding to C.
| base : base_type → type
-- A builtin array with a statically known size.
| sized_array : nat -> type → type
-- A builtin dynamically sized array.
| array : type -> type
-- | struct : struct_def -> type
| void : type

----- sigma_elim : ptr (sigma P T)
attribute [instance]
definition base_type_coe : has_coe base_type type :=
  has_coe.mk (fun bt, type.base bt)

open base_type
open type
open subtype

constant ptr : type -> Type.{1}

definition destructor (T : type) :=
  ptr T -> IO unit

definition default_destructor (T : type) : destructor T :=
  fun x, return ()

constant base_size_of (T : base_type) : nat

definition is_sized : type → Prop
| is_sized (array _) := false
| is_sized _ := true

open tactic

lemma array_T_sized_implies_T_sized :
  Π {n : nat} (T : type),
    is_sized (sized_array n T) →
    is_sized T := sorry

definition sizeof : Π (ty : type), is_sized ty -> nat
| sizeof (base bt) p := base_size_of bt
| sizeof (sized_array n t) p := n * sizeof t (array_T_sized_implies_T_sized t p)
| sizeof (array T) p := 0
| sizeof (void) p := 0

-- Allocate a sized type
constant allocate_sized
  (T : {t \ is_sized t})
  { p : is_sized (elt_of T) }
  (n : {n \ sizeof (elt_of T) p = n }) :
  (destructor (elt_of T)) -> IO (ptr (elt_of T))

-- Allocate an array type
constant allocate_array
  (T : type) {p : is_sized T} (n : { n \ sizeof T p = n }) (initial_capacity : nat) : destructor T -> IO (ptr (array T))

-- Array fns
constant index_array {T : type} (arr : ptr (array T)) (i : nat) : IO (ptr T)
definition index_array' {T : type} (arr : ptr (array T)) (i : nat) : IO (ptr T) :=
  index_array arr i

constant array_length {T : type} (array : ptr (array T)) : IO (ptr int)
constant array_capacity {T : type} (array : ptr (array T)) : IO (ptr int)

definition new : Π (T : type), IO (ptr T)
| new (array E) := allocate_array E {| subtype, elt_of := sizeof E sorry, has_property := rfl |} 256 (fun x, return ())
| new U := allocate_sized {| subtype, elt_of := U, has_property := sorry |}
                          {| subtype, elt_of := sizeof U sorry, has_property := rfl |}
                          (fun x, return ())

attribute [reducible]
definition cstring : type :=
  type.array (base char)

definition value_of : type → Type.{1}
  | value_of void := unit
  | value_of T := ptr T

-- attribute [reducible] value_of

-- A special marker for converting
definition extern (ret : type) (s : string) : list type -> Type.{1}
  | extern [] := IO (value_of ret)
  | extern (t :: ts) := (value_of t) -> extern ts
  
-- attribute [reducible] extern

-- We really need good support for Z's would be nice to define a set of system types.
constant write_nat_as_int : nat -> ptr base_type.int -> IO unit
constant read_int_as_nat : ptr base_type.int -> IO nat
constant write_char_as_char : (char : Type) -> ptr base_type.char -> IO unit
constant read_char_as_char : ptr base_type.char  -> IO char

attribute [class]
structure storable (T : Type) (U : type) :=
  (write : T -> ptr U -> IO unit)
  (read : ptr U -> IO T)

-- This is not quite right (overflow)
attribute [instance]
definition nat_storable_to_int : storable nat (base base_type.int) :=
  {| storable,
    write := write_nat_as_int,
    read := read_int_as_nat |}

attribute [instance]
definition char_storable_to_char : storable char (base base_type.char) :=
  {| storable,
    write := write_char_as_char,
    read := read_char_as_char |}

-- definition initialize {T : Type} (U : type) [S : storable T U] (value : T) : IO (ptr U) := do
--   ptr <- new U,
--   storable.write value ptr,
--   return ptr

-- We should move this to the list module
private definition enumerate_inner {A : Type}: nat → list A → list (nat × A)
| enumerate_inner i [] := []
| enumerate_inner i (x :: xs) := (i, x) :: enumerate_inner (i + 1) xs

private definition enumerate {A : Type} (xs : list A) :=
enumerate_inner 0 xs

private definition write_to_cstring' (p : ptr cstring) : list (nat × char) → IO unit
  | write_to_cstring' [] := return unit.star
  | write_to_cstring' ((i, c) :: cs) := do
    iv <- index_array p i,
    storable.write c iv,
    write_to_cstring' cs

private definition write_to_cstring (s : string) (p : ptr cstring) : IO unit :=
  write_to_cstring' p (enumerate (list.append (list.reverse s) [char.of_nat 0]))
  
-- inference errors suck
definition read_element (p : ptr cstring) (i : nat) : IO char :=
  index_array' p i >>= (@storable.read char (base char) _)

private definition read_to_string' : nat → ptr cstring → IO string
| read_to_string' 0 p := return ""
| read_to_string' (n + 1) p := do
  c <- read_element p (n + 1),
  cs <- read_to_string' n p,
  return (c :: cs)

-- HOU is killing me here
definition length {T : type} (array : ptr (array T)) : IO nat :=
  array_length array >>= (fun (len : ptr (base int)), @storable.read nat (base int) _ len)

definition capacity {T : type} (array : ptr (array T)) : IO nat :=
  array_capacity array >>= (fun (cap : ptr (base int)), @storable.read nat (base int) _ cap)

private definition read_to_string (p : ptr cstring) : IO string := do
  len <- length p,
  read_to_string' len p

attribute [instance]
definition string_storable_to_cstring : storable string cstring :=
{| storable,
  write := write_to_cstring,
  read := read_to_string |}

definition to_cstring (s : string) : IO (ptr cstring) := do
   cstr <- new cstring,
   storable.write s cstr,
   return cstr

end ffi
