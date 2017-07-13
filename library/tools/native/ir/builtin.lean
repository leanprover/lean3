/-
Copyright (c) 2017 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

inductive builtin
| cfun : name → nat → builtin
| cases : name → nat → builtin
| vm : name → builtin

meta constant native.get_builtin : name → option builtin
