Lean 4
------

We are currently developing Lean 4 in a new (private) repository.
The source code will be moved here when Lean 4 is ready.
Users should not expect Lean 4 will be backward compatible with Lean 3.

# Goals

- New compiler and C++ code generator.
- JIT compiler on top of LLVM.
- New runtime (support for unboxed values and FFI).
- New monad for accessing primitives that are currently available only in C++ (e.g., `type_context`).
- New parser and macro expander (in Lean).
- Make sure that tactics such as `simp` can be efficiently implemented in Lean.
- Fix critical issues (e.g., issue #1601).
- Fix language issues (e.g., parameters, kernel enforced private declarations, kernel support for nested inductive datatypes).
- Reduce clutter in the core lib and code base.
