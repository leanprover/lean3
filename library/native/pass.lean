import native.internal
import init.meta.expr
import init.meta.format

meta structure pass :=
  (name : string)
  (transform : expr → expr)

meta def file_name_for_dump (p : pass) :=
  (pass.name p)

-- Unit functions get optimized away, need to talk to Leo about this one.
meta def dump_pass (p : pass) (prog : expr) : expr :=
  match native.dump_format (file_name_for_dump p ++ ".pre") (to_string prog) with
  | n := let result := pass.transform p prog in
    match native.dump_format (file_name_for_dump p ++ ".post") (to_string result) with
    | m := if n = m then result else prog
    end
  end

-- Unit functions get optimized away, need to talk to Leo about this one.
meta def run_pass (p : pass) (prog : expr) : expr :=
  match native.dump_format (file_name_for_dump p ++ ".pre") (to_string prog) with
  | n := let result := pass.transform p prog in
         match native.dump_format (file_name_for_dump p ++ ".post") (to_string result) with
         | m := if n = m then result else prog
         end
  end

meta def run_passes (passes : list pass) (e : expr) : expr :=
  list.foldl (fun e pass, run_pass pass e) e passes
