/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch and Leonardo de Moura
*/
#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string>
#include <vector>
#include "util/fresh_name.h"
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/vm/vm.h"
#include "library/vm/optimize.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_format.h"
#include "library/util.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/nat_value.h"
#include "library/compiler/preprocess.h"
#include "library/native_compiler/native_compiler.h"
#include "library/native_compiler/options.h"
#include "library/native_compiler/cpp_compiler.h"
#include "library/native_compiler/extern.h"
#include "library/compiler/vm_compiler.h"
#include "library/module.h"
#include "library/native_compiler/cpp_emitter.h"
#include "library/native_compiler/used_defs.h"
#include "util/lean_path.h"
#include "util/path.h"
#include "util/path_var.h"
// #include "util/executable.h"

static std::string * g_lean_install_path = nullptr;

namespace lean {

expr mk_local(name const & n) {
    return ::lean::mk_local(n, mk_neutral_expr());
}

// Helper functions for setting up the install path on boot-up.
void initialize_install_path() {
    // 8 is the size of the string bin/lean which we want to remove from
    // the installed version of Lean.
#if defined(LEAN_EMSCRIPTEN)
    g_lean_install_path = new std::string;
#else
    auto p = get_exe_location();
    g_lean_install_path = new path(std::string(p.substr(0, p.size() - 8)));
#endif
}

path get_install_path() {
    return *g_lean_install_path;
}

extern_fn mk_lean_extern(name n, unsigned arity) {
    return extern_fn(true, n, arity);
}

extern_fn mk_extern(name n, unsigned arity) {
    return extern_fn(false, n, arity);
}

vm_obj extern_fn::to_obj() {
    throw "a";
}

// Returns the path to the Lean library based on the standard search path,
// and provided options.
std::vector<path> native_include_paths() {
    std::vector<path> paths;
    auto conf = native::get_config();
    auto native_include_path_var = path_var(conf.m_native_include_path);

    for (auto path : native_include_path_var.m_paths) {
        paths.push_back(path);
    }

    // Finally look in the default path.
    paths.push_back(get_install_path().append("include/lean_ext"));

    return paths;
}

std::vector<path> native_library_paths() {
    std::vector<path> paths;

    auto conf = native::get_config();
    auto native_library_path_var = path_var(conf.m_native_library_path);

    for (auto path : native_library_path_var.m_paths) {
        paths.push_back(path);
    }

    paths.push_back(get_install_path().append("lib"));

    return paths;
}

// Constructs a compiler with the native configuation options applied.
cpp_compiler compiler_with_native_config(native_compiler_mode mode) {
    cpp_compiler gpp;
    auto conf = native::get_config();

    if (mode == native_compiler_mode::AOT) {
        gpp = mk_executable_compiler();
        // The executable has two linkage strategies unlike the module compiler
        // we want to sometime use static linking, and sometimes dynamic.
        if (conf.m_native_dynamic) {
            gpp.link(LEAN_STATIC_LIB);
        } else {
            gpp.link(LEAN_SHARED_LIB);
        }
    } else {
        gpp = mk_shared_compiler();
    }

    auto include_paths = native_include_paths();
    auto library_paths = native_library_paths();

    // Setup include paths
    for (auto path : include_paths) {
        gpp.include_path(path.to_string());
    }

    for (auto path : library_paths) {
        gpp.library_path(path.to_string());
    }

    // Have g++ emit debug information.
    if (conf.m_native_emit_dwarf) {
        gpp.debug(true);
    }

    return gpp;
}

void add_shared_dependencies(cpp_compiler & compiler) {
    compiler.link("gmp")
            .link("pthread")
            .link("mpfr");
}

/* This function constructs a config value located in library/native/config.lean */
vm_obj mk_lean_native_config() {
    auto native_conf = native::get_config();

    lean::vm_obj dump_passes;
    if (native_conf.m_native_dump == std::string("")) {
        dump_passes = mk_vm_simple(0);
    } else {
        dump_passes = mk_vm_simple(1);
    }

    return mk_vm_constructor(0, dump_passes, mk_vm_simple(0));
}

lean::vm_obj to_lean_procs(buffer<procedure> & procs) {
    // let procs_list = [];
    vm_obj procs_list = mk_vm_simple(0);
    // procs_list = tuple :: procs_list
    for (auto & p : procs) {
        auto tuple = mk_vm_constructor(0, { to_obj(p.m_name), to_obj(p.m_code) });
        procs_list = mk_vm_constructor(1, { tuple, procs_list });
    }

    return procs_list;
}

lean::vm_obj to_lean_extern_fns(buffer<extern_fn> & extern_fns) {
    // let procs_list = [];
    vm_obj externs_list = mk_vm_simple(0);
    // procs_list = tuple :: procs_list
    for (auto & e : extern_fns) {
        auto inner_tuple = mk_vm_constructor(0, { to_obj(e.m_name), to_obj(e.m_arity) });
        auto tuple = mk_vm_constructor(0, { mk_vm_simple(e.m_in_lean_namespace), inner_tuple });
        externs_list = mk_vm_constructor(1, { tuple, externs_list });
    }

    return externs_list;
}

// std::vector<std::pair<std::string, format>>> from_files(lean::vm_obj files_obj) {
//     return std::vector();
// }

format invoke_native_compiler(
    environment const & env,
    buffer<extern_fn> & extern_fns,
    buffer<procedure> & procs)
{
    auto list_of_procs = to_lean_procs(procs);
    auto list_of_extern_fns = to_lean_extern_fns(extern_fns);
    auto conf_obj = mk_lean_native_config();

    vm_state S(env, get_global_ios().get_options());
    scope_vm_state scoped(S);

    auto compiler_name = name({"native", "compile"});
    auto cc = mk_native_closure(env, compiler_name, {});

    vm_obj fmt_obj = S.invoke(
        cc,
        conf_obj,
        list_of_extern_fns,
        list_of_procs);

    return to_format(fmt_obj);
}

void native_compile(environment const & env,
                    buffer<extern_fn> & extern_fns,
                    buffer<procedure> & procs,
                    native_compiler_mode mode) {
    std::fstream out("out.cpp", std::ios_base::out);

    // Emit externs (currently only works for builtins).
    // compiler.emit_prototypes(extern_fns);

    // for (auto & p : procs) {
    //    compiler.emit_prototype(p.m_name, p.m_code);
    // }

    auto fmt = invoke_native_compiler(env, extern_fns, procs);

    out << fmt << "\n\n";

    // For now just close this, then exit.
    out.close();

    // Get a compiler with the config specified by native options, placed
    // in the correct mode.
    auto gpp = compiler_with_native_config(mode);

    // Add all the shared link dependencies.
    add_shared_dependencies(gpp);

    gpp.file("out.cpp")
       .run();
}

void native_preprocess(environment const & env, declaration const & d, buffer<procedure> & procs) {
    lean_trace(name({"compiler", "native"}),
      tout() << "native_preprocess:" << d.get_name() << "\n";);

    // Run the normal preprocessing and optimizations.
    preprocess(env, d, procs);
}

bool is_internal_decl(declaration const & d) {
    auto n = d.get_name();
    return (n == name("_neutral_") ||
            n == name({"native_compiler", "return"}) ||
            is_internal_cnstr(mk_constant(n)) ||
            is_internal_cases(mk_constant(n)) ||
            is_internal_proj(mk_constant(n)));
}

optional<extern_fn> get_builtin(name const & n) {
    auto internal_name = get_vm_builtin_internal_name(n);
    if (internal_name) {
        switch (get_vm_builtin_kind(n)) {
            case vm_builtin_kind::VMFun: {
                return optional<extern_fn>();
            }
            case vm_builtin_kind::CFun: {
                auto arity = get_vm_builtin_arity(n);
                return optional<extern_fn>(
                    mk_lean_extern(internal_name, arity));
            }
            case vm_builtin_kind::Cases: {
                return optional<extern_fn>(
                    mk_lean_extern(internal_name, 2u));
            }
        }
        lean_unreachable();
    } else {
        return optional<extern_fn>();
    }
}

void populate_extern_fns(
    environment const & env,
    used_defs const & used,
    buffer<extern_fn> & extern_fns, bool is_library) {
    used.m_used_names.for_each([&] (name const & n) {
        if (auto builtin = get_builtin(n)) {
             // std::cout << "extern fn: " << n << std::endl;
             extern_fns.push_back(mk_lean_extern(n, builtin.value().m_arity));
        } else if (has_extern_attribute(env, n)) {
            extern_fns.push_back(mk_extern(n, 0));
        } else if (is_library) {
            extern_fns.push_back(mk_extern(n, 0));
        }
    });
}

void native_compile_module(environment const & env, buffer<declaration> decls) {
    std::cout << "compiled native module" << std::endl;

    // Preprocess the main function.
    buffer<procedure> all_procs;
    buffer<procedure> main_procs;
    buffer<extern_fn> extern_fns;

    // Compute the live set of names, we attach a callback that will be
    // invoked for every declaration encountered.
    used_defs used_names(env, [&] (declaration const & d) {
        buffer<procedure> procs;
        // The the name is an internal decl we should not add it to the live set.
        if (is_internal_decl(d)) {
            return;
        // We should skip it if its a bulitin, or a builtin_cases on.
        } else if (auto p = get_builtin(d.get_name())) {
            return;
            // extern_fns.push_back(p.value());
        } else if (auto p =  get_vm_builtin_cases_idx(env, d.get_name())) {
            return;
        } else if (has_extern_attribute(env, d.get_name())) {
            lean_unreachable()
        } else {
            native_preprocess(env, d, procs);
            for (auto pair : procs) {
                used_names.names_in_expr(pair.m_code);
                all_procs.push_back(pair);
            }
        }
    });

    // We then loop over the set of procs produced by preprocessing the
    // main function, we transitively collect all names.
    for (auto decl : decls) {
        used_names.names_in_decl(decl);
    }

    // We now need to collect every function we are choosing to
    // declare as external. We emit an extern decl for every
    // function that exists in the Lean namespace, and then
    // an extern decl for every other function, since the
    // symbols must be visible to other shared libraries
    // when loading them.
    populate_extern_fns(env, used_names, extern_fns, true);

    // Finally we assert that there are no more unprocessed declarations.
    lean_assert(used_names.stack_is_empty());

    native_compile(env, extern_fns, all_procs, native_compiler_mode::JIT);
}

void native_compile_binary(environment const & env, declaration const & d) {
    lean_trace(name("native_compile"),
        tout() << "main_fn: " << d.get_name() << "\n";);

    lean_trace(name("native_compiler"),
        tout() << "main_body: " << d.get_value() << "\n";);

    // Preprocess the main function.
    buffer<procedure> all_procs;
    buffer<procedure> main_procs;
    buffer<extern_fn> extern_fns;
    native_preprocess(env, d, main_procs);

    // Compute the live set of names, we attach a callback that will be
    // invoked for every declaration encountered.
    used_defs used_names(env, [&] (declaration const & d) {
        buffer<procedure> procs;
        if (is_internal_decl(d)) {
            return;
        } else if (auto p = get_builtin(d.get_name())) {
            return;
            // extern_fns.push_back(p.value());
        } else if (auto p =  get_vm_builtin_cases_idx(env, d.get_name())) {
            return;
        } else {
            native_preprocess(env, d, procs);
            for (auto pair : procs) {
                used_names.names_in_expr(pair.m_code);
                all_procs.push_back(pair);
            }
        }
    });

    // We then loop over the set of procs produced by preprocessing the
    // main function, we transitively collect all names.
    for (auto pair : main_procs) {
        all_procs.push_back(pair);
        used_names.names_in_preprocessed_body(pair.m_code);
    }

    populate_extern_fns(env, used_names, extern_fns, false);

    // Finally we assert that there are no more unprocessed declarations.
    lean_assert(used_names.stack_is_empty());

    native_compile(env, extern_fns, all_procs, native_compiler_mode::AOT);
}

// +void decls_to_native_compile(environment const & env, buffer<declaration> & decls) {
//  +    // module_ext const & ext = get_extension(env);
//  +    //
//  +    // // Collect all the declarations that should be compiled from this
//  +    // // module.
//  +    // for (auto decl_name : ext.m_module_decls) {
//  +    //     auto decl = env.get(decl_name);
//  +    //     if (is_noncomputable(env, decl_name) ||
//  +    //         !decl.is_definition() ||
//  +    //         is_vm_builtin_function(decl_name)) {
//  +    //             continue;
//  +    //     } else {
//  +    //         std::cout << decl.get_name() << std::endl;
//  +    //         decls.push_back(decl);
//  +    //     }
//  +    // }
//  +}

void native_compile_module(environment const & env) {
    buffer<declaration> decls;
    // TODO(Jared): bring this code back
    // decls_to_native_compile(env, decls);
    native_compile_module(env, decls);
}

struct native_module_path_modification : public modification {
    LEAN_MODIFICATION("native_module_path")

    name m_native_module_path;

    native_module_path_modification() {}
    native_module_path_modification(name const & fn) : m_native_module_path(fn) {}

    void perform(environment &) const override {
        // TODO(gabriel,jared): I have no idea what this is supposed to do.
        // ???
    }

    void serialize(serializer & s) const override {
        s << m_native_module_path;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<native_module_path_modification>(read_name(d));
    }
};

environment set_native_module_path(environment & env, name const & n) {
    return module::add(env, std::make_shared<native_module_path_modification>(n));
}

void initialize_native_compiler() {
    native::initialize_options();
    initialize_install_path();
    register_trace_class({"compiler", "native"});
    register_trace_class({"compiler", "native", "preprocess"});
    register_trace_class({"compiler", "native", "cpp_compiler"});
    native_module_path_modification::init();
}

void finalize_native_compiler() {
    native::finalize_options();
    delete g_lean_install_path;
    native_module_path_modification::finalize();
}
}
