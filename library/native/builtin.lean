inductive builtin
| cfun : name -> nat -> builtin
| cases : name -> nat -> builtin
| vm : name -> builtin

meta constant native.get_builtin : name → option builtin
