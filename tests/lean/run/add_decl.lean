
open tactic expr
run_cmd
do -- t ← mk_local_def `foo `(Type),
   let c := @const tt `foo [],
   add_inductive `foo [] 0 `(Type) [(`constr,c)]

#check foo.no_confusion
