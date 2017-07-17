import system.io
import data.buffer
import .config

namespace native

structure cpp_compiler :=
(library_paths : buffer string := buffer.nil)
(include_paths : buffer string := buffer.nil)
(files : buffer string := buffer.nil)
(link : buffer string := buffer.nil)
(cc : string := "g++")
(output : option string := none)
(debug : bool := false)
(shared : bool := false)
(pic : bool := false)
(warnings : buffer string := buffer.nil)

namespace cpp_compiler

def with_config (cfg : config) : cpp_compiler :=
{ library_paths := cfg.library_path.to_buffer,
  include_paths := cfg.include_path.to_buffer }

/-- Configure a C++ compiler in the default executable mode. -/
def mk_executable (opt_cc : option native.config := none) : cpp_compiler :=
match opt_cc with
| none := {}
| some cfg := with_config cfg
end

-- Add options here?
def mk_shared (opt_cc : option config := none) : cpp_compiler :=
match opt_cc with
| none := {}
| some cfg := with_config cfg
end

def insert_before {α : Type} (el : α) (buf : buffer α) : buffer α :=
list.to_buffer $ list.join (list.map (fun x, [el, x]) buf.to_list)

/- We should optimize this -/
def as_spawn_args (cc : cpp_compiler) : io.process.spawn_args :=
let cmd := cc.cc,
    lib_paths := insert_before "-L" cc.library_paths,
    include_paths := insert_before "-I" cc.include_paths,
    files := cc.files.to_list,
    link := insert_before "-l" cc.link,
    debug := if cc.debug then ["-debug"] else [],
    shared := if cc.shared then ["-shared"] else [],
    pic := if cc.pic then ["-fPIC"] else [],
    warnings := insert_before "-W" cc.warnings,
    output := match cc.output with
    | none := []
    | some of := ["-o", of]
    end
in {
  cmd := cmd,
  args := "-std=c++14" :: list.join [
    lib_paths.to_list,
    include_paths.to_list,
    files,
    link.to_list,
    debug,
    shared,
    pic,
    warnings.to_list,
    output
  ]
}

variable [io.interface]

def run (cc : cpp_compiler) : io unit :=
do io.print (to_string $ cc.as_spawn_args.args),
   child ← io.proc.spawn cc.as_spawn_args,
   exit_code ← io.proc.wait child,
   if exit_code = 0
   then return ()
   else io.fail "executing the C++ compiler failed"

end cpp_compiler
end native
