# Lean's Virtual Machine

## Overview

In simple terms Lean's VM is a single-threaded command-based
interpreter. As it processes a file it adds the commands it
encounters to a global environment.

The environment is, in simple terms, a map of names to pairs of
types and values. The type and value are both expressions.

Unless we are evaluating proofs we evaluate expressions in the
environment using the VM. Every expression in a command is compiled
to a form of byte code that can be executed by the VM.

## TODO Architecture

## TODO Memory

## Foreign Function Interface

Lean depends on `libffi` for it's foreign function interface on top of
`dlopen`.

The VM environment has two functions we use to load pointers to
foreign objects opened with `dlopen`:

1. `environment_load_foreign_object` which uses `vm_dynload` to call
   `dlopen` and construct a `vm_foreign_object` instance. The instance
   is added to a special map in the environment declarations.

2. `environment_bind_foreign_symbol` which uses `libffi` to create a
   `ff_cif` object from the Lean function definition. The `lib_cif`
   gets stored in the declaration with the function.

When the environment evaluates an expression that calls a function
from a foreign object it gets the `ffi_cif` for that function,
initializes the argument values on the stack, and calls the `libffi`
interface with the handle to the foreign library and the `ffi_cif`.
