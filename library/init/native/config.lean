/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude
import init.data.bool.basic

namespace native

inductive backend
| CPP
| JS

-- eventually expose all the options here
-- if you change this you change the corresponding
-- code in library/native_compiler/native_compiler.cpp
record config :=
  (debug : bool)
  (compiler_backend : option backend)

end native
