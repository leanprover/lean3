import data.string
import data.list

/- TODO @lukenels: Separate this monad stuff out of here -/
structure functor [class] (f : Type → Type) : Type :=
 (map : Π {a b: Type}, (a → b) → f a → f b)

structure monad [class] (m : Type → Type) extends functor m : Type :=
 (return : Π {a:Type}, a → m a)
 (bind : Π {a b: Type}, m a → (a → m b) → m b)

constant RealWorld : Type
constant raw_string : Type
constant string_to_raw_string : RealWorld -> string -> (RealWorld × raw_string)

constant raw_print : RealWorld -> raw_string -> (RealWorld × unit)

constant trace : forall {A : Type}, string -> A -> A

structure IO (a : Type) : Type :=
  (runIO : RealWorld → RealWorld × a)

attribute RealWorld [extern]
attribute string_to_raw_string [extern]
attribute raw_print [extern]

 -- definition functorIO [instance] : functor IO :=
 -- {| functor IO,
 --    map := λ (a b: Type) (f: a → b) (x: IO a),
 --    IO.mk (λ rw, match IO.runIO x rw with
 --                 prod.mk res rw' := prod.mk (f res) rw'
 --                 end)
 -- |}

 -- definition monadIO [instance] : monad IO :=
 -- {| monad IO,
 --    functorIO,
 --    return := λ (T:Type) (x:T),
 --      IO.mk (λ rw, prod.mk x rw),
 --    bind := λ (a b: Type) (x: IO a) (f: a → IO b),
 --      IO.mk (λ rw,
 --        match IO.runIO x rw with
 --        prod.mk res rw' := IO.runIO (f res) rw'
 --        end)
 -- |}

definition return {T : Type} (x : T) : IO T :=
    IO.mk (λ rw, prod.mk rw x)

definition bind {A B} (action : IO A) (f : A -> IO B) : IO B :=
   IO.mk (λ rw,
     -- use let bindings to get around code generation issue
     match IO.runIO action rw with
     | prod.mk rw' res := IO.runIO (f res) rw'
     end)

structure ToString [class] (A : Type) :=
  (to_string : A → string)

definition ToString_string [instance] : ToString string :=
   {| ToString,
     to_string := id |}

definition raw_print_io (rs : raw_string) : IO unit :=
      IO.mk (fun rw, raw_print rw rs)

definition print_string (s : string) : IO unit :=
   trace "print_string"
    (bind (IO.mk (fun rw, string_to_raw_string rw s)) raw_print_io)

definition string_append : string -> string -> string
 | string_append string.empty s2 := trace "string_append_empty" s2
 | string_append (string.str c cs) s2 :=
    trace "string_append_str" (string.str c (string_append cs s2))

definition to_string_list {A} [ts : ToString A]: list A -> string
   | to_string_list (list.nil) := ""
   | to_string_list (list.cons x xs) := string_append (ToString.to_string x) (to_string_list xs)

definition ToString_poly_list [instance] (A : Type) [tsA : ToString A] : ToString (list A) :=
    {| ToString,
       to_string := to_string_list |}

definition print_line {A} [ts : ToString A] (a : A) : IO unit :=
  print_string (ToString.to_string a)
