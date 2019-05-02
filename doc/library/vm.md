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
