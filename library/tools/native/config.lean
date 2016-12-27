/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.data.bool.basic

namespace native

inductive backend
| CPP
| JS

inductive compilation_mode : Type
| module : compilation_mode
| executable : compilation_mode

-- eventually expose all the options here
-- if you change this you change the corresponding
-- code in library/native_compiler/native_compiler.cpp
structure config :=
(debug : bool)
  -- this flag is invisble I don't understand why
  (mode : compilation_mode)
  (compiler_backend : option backend)

def is_executable : config -> bool
| (| _, compilation_mode.executable, _ |) := bool.tt
| _ := bool.ff

def is_module : config -> bool
| (| _, compilation_mode.module, _ |) := bool.tt
| _ := bool.ff

end native
