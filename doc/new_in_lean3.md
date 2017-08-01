# What's new in Lean 3?

Lean 3 is the latest major version of Lean. It is not backwards compatible with [Lean 2][lean2].

The main changes from Lean 2 to Lean 3 are:

- a more stable elaborator,
- a new byte-code evaluator,
- an API for metaprogramming,
- better infrastructure for automation,
- no more support for homotopy type theory (HoTT).

The rest of this document lists all the syntax changes in Lean 3. It is intended to help with porting Lean 2 code to Lean 3.

## Changed

- `print` changed to `#print`
- `check` changed to `#check`
- `eval` changed to `#reduce`
- type hierarchy changed to `Sort 0`, `Sort 1`, …
    - `Prop` is defined as `Sort 0`
    - `Type u` is defined as `Sort (u+1)`
- inductive types: `inductive T : Type := …` changed to `inductive T : Type …` (no more `:=`)
- refer to hypothesis in context by type: `` `a = b` `` changed to `‹a = b›`
- attributes: `definition foo [attr1] [attr2]` changed to `@[attr1, attr2] definition foo`
- type class instance: `definition foo [instance] : has_bar …` changed to `instance foo : has_bar …`
    - the instance name can be omitted: `instance : has_bar …`
- record construction: `{| red := 1, green := 2 |}` changed to `{ red := 1, green := 2 }`
- record update: `{| red := 1, other_color |}` changed to `{ other_color with red := 1 }`
- pattern matching: `def add | add 0 m := m …` changed to `def add | 0 m := m …` (no repeating function name)
- symmetry: `⁻¹` now refers to group inverses, not symmetry
    - instead of `H⁻¹`, use use `H⁻¹ᵉ` or `H.symm` (where `H : a = b`)
- substitution: left-hand side of `eq.subst` (`▸`) can no longer contain metavariables
    - consider using the rewrite tactic instead

## Added

- `#eval` evaluates terms by generating and executing bytecode
- `def` is a shorthand for `definition`
- `suffices` construct helps structure proofs
- `⟨…⟩` is an anonymous constructor for types with one constructor
    - _example_: `⟨a, b⟩` or `(|a, b|)` instead of `and.intro a b`
- dot syntax: `v.foo a b c` is equivalent to `T.foo v a b c` where `v : T`
    - _example_: `H.left` instead of `and.left H`
- `«a-weird.name»` refers to names with illegal characters

## Removed

- `proposition` and `corollary` (aliases for `theorem`) removed
    - `theorem`, `lemma`, and `example` remain
- `premise` (alias for `variable`) removed
- `hypothesis` and `conjecture` (aliases for `parameter`) removed
- `take` (alias for `assume`) removed
- `suppose` removed
    - instead of `suppose p`, use `assume : p`
- `obtain` removed (for now)
    - instead of `obtain (n : nat), (H : n > 1) from …,`, use `let ⟨n, H⟩ := … in`
    - the `obtain` syntax [will be supported eventually][obtain]
- `abbreviation` removed
    - use `def` instead, possibly with `@[reducible]`
- `induction` and `induction_on` (aliases for `rec` and `rec_on`) removed
- `proof … qed` syntax removed
- implicit argument syntax `!` removed
    - instead of `!H`, use `(@H _ _ …)` 
- `{…}` notation in calc removed
    - instead of `{H}`, use `by rw H` (rewrite tactic)

[lean2]: https://github.com/leanprover/lean2
[obtain]: https://groups.google.com/d/msg/lean-user/X-smxltAA9s/8FRExO7iBQAJ
