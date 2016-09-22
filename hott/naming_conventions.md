HoTT Naming Conventions
=======================


[generic naming conventions go here]

Pointed Types
-------------

We use a prefix `p` to specify that an operation/construction is pointed. For example `pequiv` is
pointed equivalences and `phomotopy` are pointed homotopies. Only if a construction only works for
pointed types and has no unpointed equivalent we omit the `p` (examples: `loop` `loopn`
`homotopy_group`). A lemma about pointed constructions repeats the `p` for every name, for example
`psusp_pequiv_psusp` or `pid_pcompose`. For notation we append `*` for the pointed version, like `Type*` (this is the universe of pointed types, not the universe considered as a pointed type), `S*` or `bool*`. For notations which only make sense pointed we don't add the star, like `Ω[n]` or `π[k]`.