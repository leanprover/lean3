/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.data.bool.basic

namespace native

inductive compilation_mode : Type
| module : compilation_mode
| executable : compilation_mode

structure config :=
(debug : bool := bool.ff)
(mode : compilation_mode := compilation_mode.module)
(compiler_backend : option string := none)
(include_path : list string)
(library_path : list string)

def is_executable (cfg : config) :=
cfg.mode = compilation_mode.executable

def is_module (cfg : config) :=
cfg.mode = compilation_mode.module

end native
