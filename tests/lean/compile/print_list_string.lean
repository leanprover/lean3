import system.io

constant managed_pointer : Type
attribute managed_pointer [extern]

definition destructor := managed_pointer -> IO unit

constant raw_allocate : RealWorld -> nat -> destructor -> prod RealWorld managed_pointer
attribute raw_allocate [extern]

definition default_destructor (ptr : managed_pointer) :=
    pure unit.star

definition allocate (size : nat) : IO managed_pointer :=
    IO.mk (fun rw, raw_allocate rw size default_destructor)

inductive ctype :=
    | int : ctype
    | char : ctype
    | pointer : ctype -> ctype

constant raw_get_line : RealWorld -> prod RealWorld raw_string
attribute raw_get_line [extern]

definition get_line : IO raw_string :=
    IO.mk raw_get_line

-- We can add partiality back in
constant raw_forever : forall {A B : Type}, RealWorld -> IO A -> prod RealWorld B
attribute raw_forever [extern]

definition forever {A B : Type} (action : IO A) : IO B :=
    IO.mk (fun rw, raw_forever rw action)

-- inductive typed_pointer : ctype -> Type :=
--    | mk_pointer : forall {ty : ctype} -> managed_pointer -> typed_pointer ty

definition main : IO unit := forever (bind get_line raw_print_io)
