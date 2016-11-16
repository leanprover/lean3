/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch and Leonardo de Moura
*/
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
#include "library/compiler/native_compiler.h"
#include "library/compiler/annotate_return.h"
#include "library/compiler/anf_transform.h"
#include "library/compiler/cf.h"
#include "library/compiler/options.h"
#include "library/compiler/cpp_compiler.h"
#include "library/compiler/vm_compiler.h"
#include "library/compiler/extern.h"
#include "library/module.h"
#include "library/vm/vm.h"
#include "cpp_emitter.h"
#include "used_names.h"
#include "util/lean_path.h"
// #include "util/executable.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

static std::string* g_lean_install_path;

namespace lean {

// Helper functions for setting up the install path on boot-up.
// TODO: this is not currently cross platform
void set_install_path(std::string s) {
    // 8 is the size of the string bin/lean which we want to remove from
    // the installed version of Lean.
    auto path = get_exe_location();
    g_lean_install_path = new std::string(path.substr(0, path.size() - 8));
}

std::string get_install_path() {
    return *g_lean_install_path;
}

extern_fn mk_lean_extern(name n, unsigned arity) {
    return extern_fn(true, n, arity);
}

extern_fn mk_extern(name n, unsigned arity) {
    return extern_fn(false, n, arity);
}

class native_compiler_fn {
public:
    environment        m_env;
    cpp_emitter m_emitter;
    native_compiler_mode m_mode;
    name_map<unsigned> m_arity_map;

    expr mk_local(name const & n) {
        return ::lean::mk_local(n, mk_neutral_expr());
    }

    void compile_global(vm_decl const & decl, unsigned nargs, expr const * args, unsigned bpz, name_map<unsigned> const & m) {
        name c_fn_name = decl.get_name();

        if (decl.get_arity() <= nargs) {
            if (decl.is_builtin()) {
                // I believe this code is currently unreachable on this path,
                // if not we should trip this assertion, and correct our
                // assumptions.
                lean_unreachable()
            } else {
                this->m_emitter.emit_c_call(c_fn_name, nargs, args, [=] (expr const & e) {
                    compile(e, bpz, m);
                });
            }
        } else {
            lean_assert(decl.get_arity() > nargs);
            auto name = decl.get_name();
            this->m_emitter.emit_c_call(name, nargs, args, [=] (expr const & e) {
                compile(e, bpz, m);
            });
        }
    }

    void compile_constant(expr const & e) {
        name const & n = const_name(e);
        if (is_neutral_expr(e)) {
            this->m_emitter.emit_sconstructor(0);
        } else if (is_unreachable_expr(e)) {
            this->m_emitter.emit_unreachable();
        } else if (n == get_nat_zero_name()) {
            this->m_emitter.emit_mpz(mpz(0));
        } else if (auto idx = is_internal_cnstr(e)) {
            this->m_emitter.emit_sconstructor(*idx);
        } else if (auto j = get_vm_builtin_cases_idx(m_env, n)) {
            // I also believe this case to unreachable, if it isn't we
            // should crash.
            lean_unreachable()
        } else if (is_uninitialized(e)) {
            this->m_emitter.emit_string("lean::vm_obj()");
        // TODO: refactor this
        } else if (get_builtin(n)) {
          buffer<expr> args;
          name_map<unsigned> nm;
          compile_to_c_call(n, args, 0u, nm, true);
        } else {
            buffer<expr> args;
            name_map<unsigned> nm;
            compile_to_c_call(n, args, 0u, nm);
        }
    }

    void compile_local(expr const & e, name_map<unsigned> const & m) {
        unsigned idx = *m.find(mlocal_name(e));
        this->m_emitter.emit_local(idx);
    }

    void compile_cases_on(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        lean_assert(is_constant(fn));
        name const & fn_name = const_name(fn);
        unsigned num;

        if (fn_name == get_nat_cases_on_name()) {
            num = 2;
        } else if (get_vm_builtin_cases_idx(m_env, fn_name)) {
            name const & I_name = fn_name.get_prefix();
            num = *inductive::get_num_intro_rules(m_env, I_name);
        } else {
            lean_assert(is_internal_cases(fn));
            num = *is_internal_cases(fn);
        }

        lean_assert(args.size() == num + 1);
        lean_assert(num >= 1);

        if (get_vm_builtin_cases_idx(m_env, const_name(fn))) {
            this->m_emitter.emit_builtin_cases_on(const_name(fn), args,  [&] (expr const & e) {
                expr b = e;
                buffer<expr> locals;
                buffer<unsigned> fields;
                name_map<unsigned> new_m = m;
                unsigned new_bpz = bpz;
                while (is_lambda(b)) {
                    name n = mk_fresh_name();
                    new_m.insert(n, new_bpz);
                    locals.push_back(mk_local(n));
                    fields.push_back(new_bpz);
                    new_bpz++;
                    b = binding_body(b);
                }
                m_emitter.emit_builtin_fields(name("args"), fields);
                b = instantiate_rev(b, locals.size(), locals.data());
                compile(b, new_bpz, new_m);
              });
          } else if (fn_name == get_nat_cases_on_name()) {
            this->m_emitter.emit_nat_cases(args[0], args[1], args[2], [&] (expr const & e) {
                expr b = e;
                buffer<expr> locals;
                buffer<unsigned> fields;
                name_map<unsigned> new_m = m;
                unsigned new_bpz = bpz;
                while (is_lambda(b)) {
                    name n = mk_fresh_name();
                    new_m.insert(n, new_bpz);
                    locals.push_back(mk_local(n));
                    fields.push_back(new_bpz);
                    new_bpz++;
                    b = binding_body(b);
                }
                m_emitter.emit_fields(args[0], fields, [&]  (expr const & e) {
                  // lean_assert(is_local(e));
                  compile(e, new_bpz, new_m);
                });
                b = instantiate_rev(b, locals.size(), locals.data());
                compile(b, new_bpz, new_m);
            });
        } else {
            this->m_emitter.emit_cases_on(name("scrut"), args, [&] (expr const & e) {
                expr b = e;
                buffer<expr> locals;
                buffer<unsigned> fields;
                name_map<unsigned> new_m = m;
                unsigned new_bpz = bpz;
                while (is_lambda(b)) {
                    name n = mk_fresh_name();
                    new_m.insert(n, new_bpz);
                    locals.push_back(mk_local(n));
                    fields.push_back(new_bpz);
                    new_bpz++;
                    b = binding_body(b);
                }
                m_emitter.emit_fields(args[0], fields, [&]  (expr const & e) {
                  // lean_assert(is_local(e));
                  compile(e, new_bpz, new_m);
                });
                b = instantiate_rev(b, locals.size(), locals.data());
                compile(b, new_bpz, new_m);
            });
        }
    }

    void compile_cnstr(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_internal_cnstr(fn));
        unsigned cidx = *is_internal_cnstr(fn);
        this->m_emitter.emit_constructor(cidx, args.size(), args.data(), [=] (expr const & e) {
            compile(e, bpz, m);
        });
    }


    void compile_proj(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        std::cout << "compiling projection: " << e << std::endl;
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_internal_proj(fn));
        unsigned idx = *is_internal_proj(fn);
        //TODO: clean up
        if (args.size() > 1) {
            this->m_emitter.emit_string("lean::invoke(");
        }
        this->m_emitter.emit_string("cfield(");
        // lean_assert(args.size() == 1);
        compile(args[0], bpz, m);
        this->m_emitter.emit_string(", ");
        this->m_emitter.emit_string((sstream() << idx).str().c_str());
        this->m_emitter.emit_string(")");
        // TODO: clean up
        if (args.size() > 1) {
            for (int i = 1; i < args.size(); i++) {
                this->m_emitter.emit_string(",");
                compile(args[i], bpz, m);
            }
            this->m_emitter.emit_string(")");
        }
    }

    void compile_to_c_call(name const & _lean_name, buffer<expr> & args, unsigned bpz, name_map<unsigned> const & m, bool is_external = false) {
      name lean_name(_lean_name);

      // Compute the post-processing arity by looking up in the arity map.
      unsigned arity;

      if (is_external) {
          auto builtin_name = get_vm_builtin_internal_name(lean_name);
          arity = *this->m_arity_map.find(builtin_name);
      } else {
          arity = *this->m_arity_map.find(lean_name);
      }

      for (auto arg : args) {
          std::cout << "\t" << arg << std::endl;
      }
      if (args.size() < arity) {
          this->m_emitter.emit_mk_native_closure(
            lean_name,
            args.size(),
            args.data(), [=] (expr const & e) {
              compile(e, bpz, m);
            });
      } else if (args.size() == arity) {
          // Note: this is kind of a hack, would like to abstract over this
          // more cleanly by doing an annotation pass on all foreign calls.

          if (is_external) {
              std::string s("lean::");
              s += get_vm_builtin_internal_name(lean_name);
              lean_name = name(s);
          }

          this->m_emitter.emit_c_call(
            lean_name,
            args.size(),
            args.data(), [=] (expr const & e) {
              compile(e, bpz, m);
            });
      } else {
        this->m_emitter.emit_oversaturated_call(
          lean_name,
          arity,
          args.size(),
          args.data(), [=] (expr const & e) {
            compile(e, bpz, m);
          });
      }
    }

    void compile_fn_call(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        if (!is_constant(fn)) {
            if (is_local(fn)) {
                auto local_no = *m.find(mlocal_name(fn));
                this->m_emitter.emit_local_call(local_no, args.size(), args.data(), [=] (expr const & e) {
                    compile(e, bpz, m);
                });
            } else {
                // The previous passes should of made it so this case is
                // impossible.
                lean_unreachable()
            }
        } else if (is_constant(fn)) {
            if (is_return_expr(fn)) {
                this->m_emitter.emit_return([&] () {
                    compile(args[0], bpz, m);
                });
            } else if (auto n = get_vm_builtin_internal_name(const_name(fn))) {
                // Be careful here, we need to ensure that we pass the
                // Lean name here, since certain types of calls still
                // pass through the VM.
                compile_to_c_call(const_name(fn), args, bpz, m, true);
            } else if (is_neutral_expr(fn)) {
                this->m_emitter.emit_sconstructor(0);
            } else {
                compile_to_c_call(const_name(fn), args, bpz, m);
            }
        } else {
            // The previous passes should of made it so this case is
            // impossible.
            lean_unreachable();
        }
    }

    void compile_app(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);

        if (is_return_expr(fn)) {
            this->m_emitter.emit_return([&] () {
                compile(args[0], bpz, m);
            });
        } else if (is_initialize(fn)) {
            auto location = args[0];
            auto cases_on = args[1];
            auto cont = args[2];
            name_map<unsigned> new_m = m;
            auto new_bpz = bpz;
            // We should figure out how to do something smarter here,
            // we just *know* that the bpz we last consumed is
            // the unitialized binding.
            new_m.insert(mlocal_name(location), new_bpz - 1);
            compile(cases_on, new_bpz, new_m);
            this->m_emitter.emit_indented(";\n");
            compile(cont, new_bpz, new_m);
        } else if (is_store(fn)) {
            compile(args[0], bpz, m);
            this->m_emitter.emit_string(" = ");
            compile(args[1], bpz, m);
            this->m_emitter.emit_string(";\n");
        } else if (
            (is_constant(fn) && get_vm_builtin_cases_idx(m_env, const_name(fn))) ||
            is_internal_cases(fn) || is_constant(fn, get_nat_cases_on_name())) {
            compile_cases_on(e, bpz, m);
        } else if (is_internal_cnstr(fn)) {
            compile_cnstr(e, bpz, m);
        } else if (is_internal_proj(fn)) {
            compile_proj(e, bpz, m);
        } else if (is_constant(fn) && has_extern_attribute(m_env, const_name(fn)))  {
            compile_fn_call(e, bpz, m);
        } else {
            // should probahly signal an error here, and explicitly match,
            // any other case ane report an error
            compile_fn_call(e, bpz, m);
        }
    }

    void compile_let(expr e, unsigned bpz, name_map<unsigned> const & m) {
        unsigned counter = 0;
        buffer<expr> locals;
        name_map<unsigned> new_m = m;

        while (is_let(e)) {
            counter++;
            this->m_emitter.emit_local_binding(bpz, [=] {
              compile(instantiate_rev(let_value(e), locals.size(), locals.data()), bpz, new_m);
            });
            name n = mk_fresh_name();
            new_m.insert(n, bpz);
            locals.push_back(mk_local(n));
            bpz++;
            e = let_body(e);
        }
        lean_assert(counter > 0);
        compile(instantiate_rev(e, locals.size(), locals.data()), bpz, new_m);
    }

    void compile_macro(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        if (is_nat_value(e)) {
            auto value = get_nat_value_value(e);
            this->m_emitter.emit_mk_nat(value);
        } else if (is_annotation(e)) {
            compile(get_annotation_arg(e), bpz, m);
        } else {
            throw exception(sstream() << "code generation failed, unexpected kind of macro has been found: '"
                            << macro_def(e).get_name() << "'");
        }
    }

    void compile(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        // std::cout << "compile: " << e << std::endl;
        switch (e.kind()) {
        case expr_kind::Var:      lean_unreachable();
        case expr_kind::Sort:     lean_unreachable();
        case expr_kind::Meta:     lean_unreachable();
        case expr_kind::Pi:       lean_unreachable();
        case expr_kind::Lambda:   lean_unreachable();
        case expr_kind::Macro:    compile_macro(e, bpz, m);  break;
        case expr_kind::Constant: compile_constant(e);       break;
        case expr_kind::Local:    compile_local(e, m);       break;
        case expr_kind::App:      compile_app(e, bpz, m);    break;
        case expr_kind::Let:      compile_let(e, bpz, m);    break;
        }
    }

    unsigned get_arity(expr e) {
        unsigned r = 0;
        while (is_lambda(e)) {
            r++;
            e = binding_body(e);
        }
        return r;
    }

public:
    native_compiler_fn(environment const & env, native_compiler_mode mode):
        m_env(env), m_emitter(cpp_emitter(std::string("out.cpp"))) {}

    void emit_headers() {
        this->m_emitter.emit_headers();
    }

    void emit_main(buffer<pair<name, expr>> const & procs) {
        auto conf = native::get_config();
        name main_fn(conf.m_native_main_fn);
        this->m_emitter.emit_main(main_fn, [&] () {
            for (auto & p : procs) {
                this->m_emitter.emit_declare_vm_builtin(p.first);
            }
        }, [&] () {
            buffer<expr> args;
            auto unit = mk_neutral_expr();
            args.push_back(unit);

            // Make sure to invoke the C call machinery since it is non-deterministic
            // which case we enter here.
            compile_to_c_call(main_fn, args, 0, name_map<unsigned>());
        });
    }

    // Not the most effcient, need to do two loops.
    void emit_prototypes(buffer<extern_fn> fns) {
        buffer<extern_fn> in_lean_namespace;
        buffer<extern_fn> rest;

        for (auto fn : fns) {
            if (fn.m_in_lean_namespace) {
                in_lean_namespace.push_back(fn);
            } else {
                rest.push_back(fn);
            }
        }

        this->m_emitter.emit_string("namespace lean {\n");

        for (auto fn : in_lean_namespace) {
            if (get_vm_builtin_cases_idx(m_env, fn.m_name)) {
                auto np = get_vm_builtin_internal_name(fn.m_name);
                lean_assert(np);
                this->m_emitter.emit_string("unsigned ");
                this->m_emitter.mangle_name(fn.m_name);
                this->m_emitter.emit_string("(lean::vm_obj const & o, buffer<lean::vm_obj> & data);\n");
            } else {
                this->m_emitter.emit_prototype(fn.m_name, fn.m_arity);
            }

        }
        this->m_emitter.emit_string("}\n\n");
        // We should be really generating things with C linkage to make
        // interfacing with non-cpp stuff possible.
        // this->m_emitter.emit_string("extern \"C\" {\n");
        for (auto fn : rest) {
            if (get_vm_builtin_cases_idx(m_env, fn.m_name)) {
                auto np = get_vm_builtin_internal_name(fn.m_name);
                lean_assert(np);
                this->m_emitter.emit_string("unsigned ");
                this->m_emitter.mangle_name(fn.m_name);
                this->m_emitter.emit_string("(lean::vm_obj const & o, buffer<lean::vm_obj> & data);\n");
            } else {
                this->m_emitter.emit_prototype(fn.m_name, fn.m_arity);
            }
        }
        // this->m_emitter.emit_string("}\n\n");
    }

    void operator()(name const & n, expr e) {
        buffer<expr> locals;
        buffer<unsigned> local_nums;
        unsigned bpz   = 0;
        unsigned arity = get_arity(e);
        unsigned i     = arity;
        name_map<unsigned> m;
        while (is_lambda(e)) {
            name n = mk_fresh_name();
            i--;
            m.insert(n, i);
            locals.push_back(mk_local(n));
            local_nums.push_back(i);
            bpz++;
            e = binding_body(e);
        }
        e = instantiate_rev(e, locals.size(), locals.data());
        this->m_emitter.emit_decl(n, local_nums, e, [=] (expr e) {
            compile(e, bpz, m);
        });
    }

    void emit_prototype(name const & n, expr e) {
        this->m_emitter.emit_prototype(n, get_arity(e));
    }

    void populate_arity_map(buffer<pair<name, expr>> const & procs) {
        for (auto & p : procs) {
            m_arity_map.insert(p.first, get_arity(p.second));
        }
    }

    void populate_arity_map(buffer<extern_fn> const & procs) {
        for (auto & p : procs) {
            m_arity_map.insert(p.m_name, p.m_arity);
        }
    }
};

// Returns the path to the Lean library based on the standard search path,
// and provided options.
std::vector<std::string> native_include_paths() {
    std::vector<std::string> paths;
    auto conf = native::get_config();
    auto native_include_path = std::string(conf.m_native_include_path);

    // std::cout << native_include_path << std::endl;

    // // TODO: support general path parsing here
    if (native_include_path.compare("") == 0)  {
        // Finally look in the default path.
        paths.push_back(get_install_path() + "include/lean_ext");
    } else {
        paths.push_back(native_include_path);
    }

    return paths;
}

std::vector<std::string> native_library_paths() {
    std::vector<std::string> paths;

    auto conf = native::get_config();
    auto native_library_path = std::string(conf.m_native_library_path);

    // // TODO: support general path parsing here
    if (native_library_path.compare("") == 0) {
        // Finally look in the default path.
        paths.push_back(get_install_path() + "lib");
    } else {
        paths.push_back(native_library_path);
    }

    return paths;
}

// Constructs a compiler with the native configuation options applied.
cpp_compiler compiler_with_native_config(native_compiler_mode mode) {
    cpp_compiler gpp;

    if (mode == native_compiler_mode::AOT) {
        gpp = mk_executable_compiler();
    } else {
        gpp = mk_shared_compiler();
    }

    auto conf = native::get_config();

    auto include_paths = native_include_paths();
    auto library_paths = native_library_paths();

    // Setup include paths
    for (auto path : include_paths) {
        gpp.include_path(path);
    }

    for (auto path : library_paths) {
        gpp.library_path(path);
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

void native_compile(environment const & env,
                    buffer<extern_fn> & extern_fns,
                    buffer<pair<name, expr>> & procs,
                    native_compiler_mode mode) {
    native_compiler_fn compiler(env, mode);

    buffer<name> ns;
    compiler.populate_arity_map(procs);
    compiler.populate_arity_map(extern_fns);

    // Emit the header includes.
    compiler.emit_headers();

    // Emit externs (currently only works for builtins).
    compiler.emit_prototypes(extern_fns);

    for (auto & p : procs) {
        compiler.emit_prototype(p.first, p.second);
    }

    // First we convert for Lean ...
    vm_obj procs_list = mk_vm_simple(0);
    for (auto & p : procs) {
        std::cout << p.first << std::endl;
        std::cout << p.second << std::endl;
        auto tuple = mk_vm_constructor(0, { to_obj(p.first), to_obj(p.second) });
        procs_list = mk_vm_constructor(1, { tuple, procs_list });
    }

    vm_state S(env);
    auto compiler_name = name({"native", "compile"});
    auto cc = mk_native_closure(env, compiler_name, {});

    std::fstream lean_output("out.lean.cpp", std::ios_base::out);

    vm_obj result = S.invoke(cc, procs_list);
    auto fmt = to_format(result);
    lean_output << "ir:\n";
    lean_output << fmt << std::endl;
    std::string fn = (sstream() << fmt << "\n\n").str();
    compiler.m_emitter.emit_string(fn.c_str());

    if (mode == native_compiler_mode::AOT) {
        compiler.emit_main(procs);
    }

    // Get a compiler with the config specified by native options, placed
    // in the correct mode.
    auto gpp = compiler_with_native_config(mode);

    // Add all the shared link dependencies.
    add_shared_dependencies(gpp);

    gpp.file("out.cpp")
       .run();
}

void native_preprocess(environment const & env, declaration const & d, buffer<pair<name, expr>> & procs) {
    lean_trace(name({"compiler", "native"}),
      tout() << "native_preprocess:" << d.get_name() << "\n";);

    buffer<pair<name, expr>> raw_procs;
    // Run the normal preprocessing and optimizations.
    preprocess(env, d, raw_procs);

    // std::cout << "Found some user code:" << decl.get_value() << std::endl;
    // Run the native specific optimizations.
    for (auto proc : raw_procs) {
        auto anf_body = anf_transform(env, proc.second);
        lean_trace(name({"compiler", "native", "preprocess"}),
          tout() << "anf_body:" << anf_body << "\n";);
        auto cf_body = cf(env, anf_body);
        lean_trace(name({"compiler", "native", "preprocess"}),
          tout() << "cf_body:" << cf_body << "\n";);
        auto annotated_body = annotate_return(env, cf_body);
        lean_trace(name({"native_compiler", "preprocess"}),
          tout() << "annotated_body:" << annotated_body << "\n";);

        pair<name, expr> p = pair<name, expr>(proc.first, annotated_body);
        procs.push_back(p);
    }
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
    } else {
        return optional<extern_fn>();
    }
}

void native_compile_module(environment const & env, buffer<declaration> decls) {
    std::cout << "compiled native module" << std::endl;

    // Preprocess the main function.
    buffer<pair<name, expr>> all_procs;
    buffer<pair<name, expr>> main_procs;
    buffer<extern_fn> extern_fns;

    // Compute the live set of names, we attach a callback that will be
    // invoked for every declaration encountered.
    used_defs used_names(env, [&] (declaration const & d) {
        buffer<pair<name, expr>> procs;
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
                used_names.names_in_expr(pair.second);
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
    used_names.m_used_names.for_each([&] (name const & n) {
        std::cout << n << std::endl;
        // TODO: unify this
        if (auto builtin = get_builtin(n)) {
             // std::cout << "extern fn" << n << std::endl;
             extern_fns.push_back(builtin.value());
        } else if (auto i = get_vm_builtin_cases_idx(env, n)) {
             auto arity = 2; // are these always exactly two arity?
             extern_fns.push_back(mk_lean_extern(n, arity));
        } else if (has_extern_attribute(env, n)) {
            extern_fns.push_back(mk_extern(n, 0));
        } else {
            extern_fns.push_back(mk_extern(n, 0));
        }
    });

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
    buffer<pair<name, expr>> all_procs;
    buffer<pair<name, expr>> main_procs;
    buffer<extern_fn> extern_fns;
    native_preprocess(env, d, main_procs);

    // Compute the live set of names, we attach a callback that will be
    // invoked for every declaration encountered.
    used_defs used_names(env, [&] (declaration const & d) {
        buffer<pair<name, expr>> procs;
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
                used_names.names_in_expr(pair.second);
                all_procs.push_back(pair);
            }
        }
    });

    // We then loop over the set of procs produced by preprocessing the
    // main function, we transitively collect all names.
    for (auto pair : main_procs) {
        all_procs.push_back(pair);
        used_names.names_in_preprocessed_body(pair.second);
    }

    used_names.m_used_names.for_each([&] (name const & n) {
        // TODO: unify this, get_builtin should probably get vm_builtin_cases as well.
        if (auto builtin = get_builtin(n)) {
            // std::cout << "extern fn" << n << std::endl;
            extern_fns.push_back(builtin.value());
        } else if (auto i = get_vm_builtin_cases_idx(env, n)) {
            // I believe the arity of a builtin cases on implementation
            // should always be 2.
            auto arity = 2u;
            extern_fns.push_back(mk_lean_extern(n, arity));
        } else if (has_extern_attribute(env, n)) {
            // get_arity(env.get(n).get_
            extern_fns.push_back(mk_extern(n, 2));
        }
    });

    // Finally we assert that there are no more unprocessed declarations.
    lean_assert(used_names.stack_is_empty());

    native_compile(env, extern_fns, all_procs, native_compiler_mode::AOT);
}

void native_compile_module(environment const & env) {
    buffer<declaration> decls;
    decls_to_native_compile(env, decls);
    native_compile_module(env, decls);
}

// Setup for the storage of native modules to .olean files.
static std::string *g_native_module_key = nullptr;

static void native_module_reader(
    deserializer & d,
    shared_environment & senv,
    std::function<void(asynch_update_fn const &)> &,
    std::function<void(delayed_update_fn const &)> &)
{
    name fn;
    d >> fn;
    std::cout << "reading native module from meta-data: " << fn << std::endl;
    // senv.update([&](environment const & env) -> environment {
    //     vm_decls ext = get_extension(env);
    //     // ext.update(fn, code_sz, code.data());
    //     // return update(env, ext);
    //     return
    // });
}

environment set_native_module_path(environment & env, name const & n) {
    return module::add(env, *g_native_module_key, [=] (environment const & e, serializer & s) {
        std::cout << "writing out" << n << std::endl;
        s << n;
        native_compile_module(e);
    });
}

void initialize_native_compiler() {
    native::initialize_options();
    register_trace_class({"compiler", "native"});
    register_trace_class({"compiler", "native", "preprocess"});
    g_native_module_key = new std::string("native_module_path");
    register_module_object_reader(*g_native_module_key, native_module_reader);
}

void finalize_native_compiler() {
    native::finalize_options();
    delete g_native_module_key;
}
}
