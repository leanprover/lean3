/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.data.bool.basic

namespace native

structure config :=
(debug : bool := bool.ff)
(backend : string := "c++")
(include_path : list string)
(library_path : list string)

open tactic

meta def load_config : tactic config :=
do opts ← get_options,
   let lib_path := opts.get_string `native.library_path "" ,
   let inc_path := opts.get_string `native.include_path "",
   let backend := opts.get_string `native.backend "c++",
   tactic.trace lib_path,
   tactic.trace inc_path,
   -- TODO(@jroesch) do path parsing here
   return {
     library_path := [lib_path],
     include_path := [inc_path],
     backend := backend,
  }

end native
