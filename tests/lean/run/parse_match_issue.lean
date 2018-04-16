@[irreducible] def parse_m (r σ) := except_t string $ reader_t r $ state σ

namespace parse_m
section
local attribute [reducible] parse_m

instance (r σ) : monad (parse_m r σ) := by apply_instance
instance (r σ) : monad_run _ (parse_m r σ) := by apply_instance
instance (r σ) : monad_reader r (parse_m r σ) := by apply_instance
end

def run {r σ α} (cfg : r) (st : σ) (x : parse_m r σ α) :=
let r := monad_run.run x in r cfg st

variables {r σ α γ : Type} (cfg : r) (st : σ)

protected def run_cont {β} (x : parse_m r σ α) (cont : σ → α → except string β) : except string β :=
match parse_m.run cfg st x with
| (except.ok a, st)   := cont st a
| (except.error e, _) := except.error e
end

local attribute [simp] parse_m.run_cont parse_m.run
attribute [reducible]
  parse_m.monad_run except_t.monad_run state_t.monad_run reader_t.monad_run id.monad_run

local attribute [reducible] parse_m

@[simp] lemma run_cont_read (p : σ → r → except string γ) :
  parse_m.run_cont cfg st read p = p st cfg :=
begin simp [read] end

end parse_m
