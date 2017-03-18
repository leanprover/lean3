import .io
import init.data.list.basic

namespace process
-- Is there a way to remove meta constants from here?
meta constant builder : Type

inductive stdio
| piped
| inherit
| null

meta constant builder.new (cmd : string) : io builder

/-- Add an argument to pass to the process. -/
meta constant builder.arg : builder → string → io unit

/-- Configuration for the process's stdin handle. -/
meta constant builder.stdin : builder → stdio → io unit

/-- Configuration for the process's stdout handle. -/
meta constant builder.stdout : builder → stdio → io unit

/-- Configuration for the process's stderr handle. -/
meta constant builder.stderr : builder → stdio → io unit

meta inductive pipe.mode
| read
| write

meta constant pipe : pipe.mode → Type

open pipe.mode

meta constant pipe.write {n : nat} : pipe write → array char n → io unit
meta constant pipe.read {n : nat} : pipe read → array char n → io nat

/-- A representation of an external running or completed child process. -/
meta inductive child : Type
meta constant child.stdin : child → io (pipe pipe.mode.write)
meta constant child.stdout : child → io (pipe pipe.mode.read)
meta constant child.stderr : child → io (pipe pipe.mode.read)

constant foo : forall {a} {i : nat}, ¬i < list.length ([] : list a)

constant needed_arith {x y : nat} : x < y + 1 -> x - 1 < y

def ith {α} : Π (l : list α) (i : nat), i < list.length l → α
| []        i        h := absurd h foo -- (not_lt_zero i)
| (a::ains) 0        h := a
| (a::ains) (i + 1) h := ith ains i (needed_arith h) -- (lt_of_succ_lt_succ h)

def list.to_fin_map {α} : forall (xs : list α), (fin (list.length xs) → α) :=
  fun f, begin
    intros,
    cases a,
    apply ith,
    exact is_lt,
  end

def array.from_list {α} (xs : list α) : array α (xs^.length) :=
  array.mk (list.to_fin_map xs)

def array.from_string (xs : list char) : array char (xs^.reverse^.length) :=
  array.mk (list.to_fin_map xs^.reverse)

/-- Executes the command as a child process. -/
meta constant builder.spawn : builder → io child

end process
