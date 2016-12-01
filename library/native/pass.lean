import native.internal
import native.procedure
import init.meta.expr
import init.meta.format

meta structure pass :=
  (name : string)
  (transform : procedure → procedure)

meta def file_name_for_dump (p : pass) :=
  (pass.name p)

-- Unit functions get optimized away, need to talk to Leo about this one.
meta def run_pass (p : pass) (proc : procedure) : (format × procedure × format) :=
  let result := pass.transform p proc in (to_string proc, result, to_string result)

meta def collect_dumps {A : Type} : list (format × A × format) → format × list A × format
| [] := (format.nil, [], format.nil)
| ((pre, body, post) :: fs) :=
  let (pre', bodies, post') := collect_dumps fs
  in (pre ++ format.line ++ format.line ++ pre',
      body :: bodies,
      post ++ format.line ++ format.line ++ post')

meta def inner_loop (p : pass) (es : list procedure) : list procedure :=
  let (pre, bodies, post) := collect_dumps (list.map (fun e, run_pass p e) es) in
  match native.dump_format (file_name_for_dump p ++ ".pre") pre with
  | n := match native.dump_format (file_name_for_dump p ++ ".post") post with
         | m := if n = m then bodies else bodies
         end
  end

meta def run_passes (passes : list pass) (procs : list procedure) : list procedure :=
  list.foldl (fun pass procs, inner_loop procs pass) procs passes
