 inductive RealWorld : Type :=
 | mk : RealWorld

structure IO (a : Type) : Type :=
   (run : RealWorld → RealWorld × a)

constant raw_string : Type

constant extern_string_to_raw_string : RealWorld -> string -> prod RealWorld raw_string
constant extern_raw_print : RealWorld -> raw_string -> prod RealWorld unit

definition string_to_raw_string (s : string) : IO raw_string :=
  IO.mk (fun rw, extern_string_to_raw_string rw s)

definition raw_print (s : raw_string) : IO unit :=
  IO.mk (fun rw, extern_raw_print rw s)

-- definition put_string (s : string) : IO unit :=

definition bind {A B} (ma : IO A) (f : A -> IO B): IO B :=
   IO.mk (fun rw, prod.rec_on ((IO.run ma) rw) (fun rw' a, IO.run (f a) rw'))


notation ` do ` binder ` <- ` y `;` r:(scoped:1 z, z) := bind y r
-- attribute string_to_raw_string [extern]
-- attribute raw_print [extern]

definition print_string (s : string) : IO unit :=
   do rs <- string_to_raw_string s ;
   raw_print rs


noncomputable definition main : IO unit :=
    print_string "Hello Lean!"
