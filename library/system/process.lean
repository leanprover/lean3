import .io
import init.data.list.basic
import system.read

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

open pipe

meta constant pipe.write {n : nat} : pipe mode.write → array char n → io unit
-- Read takes a buffer which it will try to reuse for perf.
meta constant pipe.read {n : nat} : pipe mode.read → array char n → io (nat × array char n)

meta instance : has_read (pipe mode.read) :=
  ⟨ @pipe.read ⟩

/-- A representation of an external running or completed child process. -/
meta inductive child : Type
meta constant child.stdin : child → io (pipe pipe.mode.write)
meta constant child.stdout : child → io (pipe pipe.mode.read)
meta constant child.stderr : child → io (pipe pipe.mode.read)

/-- Executes the command as a child process. -/
meta constant builder.spawn : builder → io child

end process
