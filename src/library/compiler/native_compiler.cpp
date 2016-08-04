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
#include "library/util.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/nat_value.h"
#include "library/compiler/preprocess.h"
#include "library/compiler/native_compiler.h"
#include "library/compiler/annotate_return.h"
#include "library/compiler/anf_transform.h"
#include "library/compiler/cf.h"
#include "library/compiler/cpp_compiler.h"
#include "library/compiler/vm_compiler.h"
#include "config.h"
#include "cpp_emitter.h"
#include "used_names.h"
#include "library/compiler/extern.h"
#include "library/vm/vm.h"
#include "util/executable.h"
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
    auto path = executable();
    g_lean_install_path = new std::string(path.substr(0, path.size() - 8));
}

std::string get_install_path() {
    return *g_lean_install_path;
}

optional<extern_fn> get_builtin(name const & n);

struct extern_fn {
    bool m_in_lean_namespace;
    name m_name;
    unsigned m_arity;
    extern_fn(bool in_lean_namespace, name n, unsigned arity) :
        m_in_lean_namespace(in_lean_namespace), m_name(n), m_arity(arity) {}
};

extern_fn mk_lean_extern(name n, unsigned arity) {
    return extern_fn(true, n, arity);
}

extern_fn mk_extern(name n, unsigned arity) {
    return extern_fn(false, n, arity);
}

class native_compiler_fn {
    environment        m_env;
    config & m_conf;
    cpp_emitter m_emitter;
    native_compiler_mode m_mode;
    name_map<unsigned> m_arity_map;

    expr mk_local(name const & n) {
        return ::lean::mk_local(n, mk_neutral_expr());
    }

    void compile_global(vm_decl const & decl, unsigned nargs, expr const * args, unsigned bpz, name_map<unsigned> const & m) {
        name c_fn_name = decl.get_name();
        // if (decl.is_constant_assumption()) {
        //     c_fn_name = get_vm_builtin_internal_name(decl.get_name());
        // } else {
        //     c_fn_name = decl.get_name();
        // }

        if (decl.get_arity() <= nargs) {
            if (decl.is_builtin()) {
                throw exception("NYI built-in call");
                // emit(mk_invoke_builtin_instr(decl.get_idx()));
            } else {
                this->m_emitter.emit_c_call(c_fn_name, nargs, args, [=] (expr const & e) {
                    compile(e, bpz, m);
                });
            }
        } else {
            lean_assert(decl.get_arity() > nargs);
            // TODO: Not sure about this case.
            auto name = decl.get_name();
            this->m_emitter.emit_c_call(name, nargs, args, [=] (expr const & e) {
                compile(e, bpz, m);
            });
        }
    }
    //
    [[ noreturn ]] void throw_unknown_constant(name const & n) {
        throw exception(sstream() << "code generation failed, VM does not have code for '" << n << "'");
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
            std::cout << "got the index" << j.value() << std::endl;
        } else if (is_uninitialized(e)) {
            this->m_emitter.emit_string("lean::vm_obj()");
        } else {
          buffer<expr> args;
          name_map<unsigned> nm;
          compile_to_c_call(n, args, 0u, nm);
        }
        //     compile_global(*decl, 0, nullptr, 0, name_map<unsigned>());
        // } else {
        //     throw_unknown_constant(n);
        // }
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
                m_emitter.emit_builtin_fields(name("args"), fields, [&] (expr const & e) {
                  // lean_assert(is_local(e));
                  compile(e, new_bpz, new_m);
                  new_bpz++;
                });
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
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_internal_proj(fn));
        unsigned idx = *is_internal_proj(fn);
        //TODO: clean up
        this->m_emitter.emit_string("cfield(");
        lean_assert(args.size() == 1);
        compile(args[0], bpz, m);
        this->m_emitter.emit_string(", ");
        this->m_emitter.emit_string((sstream() << idx).str().c_str());
        this->m_emitter.emit_string(")");
    }

    void compile_to_c_call(name const & n_, buffer<expr> & args, unsigned bpz, name_map<unsigned> const & m, bool is_external = false) {
      name n = n_;

      unsigned arity;
      this->m_arity_map.for_each([&] (name const & n, unsigned const & i) {
          // std::cout << "entry: " << n.to_string("+") <<  (n == n_) << std::endl;
          if (n == n_) {
            arity = i;
          }
      });

      // std::cout << "name:" << n.to_string("&") << std::endl;
      // I don't understand, this, temporary hack to get around it,
      // terrible performance.
      // lean_assert(this->m_arity_map.contains(n));
      //unsigned arity = *this->m_arity_map.find(n);

      if (args.size() < arity) {
          this->m_emitter.emit_mk_native_closure(
            n,
            args.size(),
            args.data(), [=] (expr const & e) {
              compile(e, bpz, m);
            });
      } else if (args.size() == arity) {
          // Note: this is kind of a hack, would like to abstract over this
          // more cleanly by doing an annotation pass on all foreign calls.
          if (is_external) {
            std::string s("lean::");
            s += n.to_string("");
            n = name(s);
          }

          this->m_emitter.emit_c_call(
            n,
            args.size(),
            args.data(), [=] (expr const & e) {
              compile(e, bpz, m);
            });
      } else {
        this->m_emitter.emit_oversaturated_call(
          n,
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
                std::cout << "not a constant:" << fn << std::endl;
                throw exception("NYI call should only take constant arg");
            }
        } else if (is_constant(fn)) {
            if (is_return_expr(fn)) {
                this->m_emitter.emit_return([&] () {
                    compile(args[0], bpz, m);
                });
            } else if (auto n = get_vm_builtin_internal_name(const_name(fn))) {
                compile_to_c_call(n, args, bpz, m, true);
            } else if (is_neutral_expr(fn)) {
                this->m_emitter.emit_sconstructor(0);
            } else {
                compile_to_c_call(const_name(fn), args, bpz, m);
            }
        } else {
            lean_unreachable();
        }
    }

    void compile_app(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        // expr const & fn = get_app_fn(e);
        expr const & fn = get_app_args(e, args);
        // std::cout << "compile_app: " << fn << std::endl;

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
        } else {
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
    native_compiler_fn(environment const & env, config & conf, native_compiler_mode mode):
        m_env(env), m_conf(conf), m_emitter(cpp_emitter(std::string("out.cpp"))) {}

    void emit_headers() {
        this->m_emitter.emit_headers();
    }

    void emit_main(buffer<pair<name, expr>> const & procs) {
        name main_fn(this->m_conf.m_main_fn);
        this->m_emitter.emit_main(main_fn, [&] () {
            for (auto & p : procs) {
                this->m_emitter.emit_declare_vm_builtin(p.first);
            }
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

        this->m_emitter.emit_string("extern \"C\" {\n");
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
        this->m_emitter.emit_string("}\n\n");
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

void native_compile(environment const & env,
                    config & conf,
                    buffer<extern_fn> & extern_fns,
                    buffer<pair<name, expr>> & procs,
                    native_compiler_mode mode) {
    native_compiler_fn compiler(env, conf, mode);

    compiler.populate_arity_map(procs);
    compiler.populate_arity_map(extern_fns);

    // Emit the header includes.
    compiler.emit_headers();

    // Emit externs (currently only works for builtins).
    compiler.emit_prototypes(extern_fns);

    for (auto & p : procs) {
        compiler.emit_prototype(p.first, p.second);
    }

    // auto compiler_name = name({"backend", "compiler"});
    // auto cc = env.get(compiler_name);
    // std::cout << cc.get_value() << std::endl;
    // vm_state S(env);

    // std::fstream lean_out_file("out.lean.cpp", std::ios_base::out);

    // Iterate each processed decl, emitting code for it.
    for (auto & p : procs) {
        lean_trace(name({"native_compiler"}), tout() << "" << p.first << "\n";);
        name & n = p.first;
        expr body = p.second;
        // vm_obj result = S.invoke(compiler_name, to_obj(p.second));
        // lean_out_file << to_string(result) << std::endl;
        compiler(n, body);
    }

    // lean_out_file.flush();
    // lean_out_file.close();

    if (mode == native_compiler_mode::AOT) {
        compiler.emit_main(procs);
    }

    cpp_compiler gpp;
    std::string lean_install_path = get_install_path();

    gpp.include_path(lean_install_path + "include/lean_ext")
      .file("out.cpp")
      // Example of option right here, dynamically or statically link Lean?
      .file(lean_install_path + "lib/libleanstatic.a")
      .link("gmp")
      .link("pthread")
      .link("mpfr")
      .debug(true)
      .run();
}

void native_preprocess(environment const & env, declaration const & d, buffer<pair<name, expr>> & procs) {
    lean_trace(name("native_compiler"),
      tout() << "native_preprocess:" << d.get_name() << "\n";);

    buffer<pair<name, expr>> raw_procs;
    // Run the normal preprocessing and optimizations.
    preprocess(env, d, raw_procs);

    // std::cout << "Found some user code:" << decl.get_value() << std::endl;
    // Run the native specific optimizations.
    for (auto proc : raw_procs) {
        auto anf_body = anf_transform(env, proc.second);
        lean_trace(name({"native_compiler", "preprocess"}),
          tout() << "anf_body:" << anf_body << "\n";);
        auto cf_body = cf(env, anf_body);
        lean_trace(name({"native_compiler", "preprocess"}),
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
    if (internal_name && get_vm_builtin_kind(n) == vm_builtin_kind::CFun) {
        auto arity = get_vm_builtin_arity(n);
        return optional<extern_fn>(
            mk_lean_extern(internal_name, arity));
    } else {
        return optional<extern_fn>();
    }
}

void native_compile_module(environment const & env, config & conf, buffer<declaration> decls) {
    std::cout << "compiled native module" << std::endl;

    // Preprocess the main function.
    buffer<pair<name, expr>> all_procs;
    buffer<pair<name, expr>> main_procs;
    buffer<extern_fn> extern_fns;

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
    for (auto decl : decls) {
        used_names.names_in_decl(decl);
    }

    used_names.m_used_names.for_each([&] (name const & n) {
        std::cout << n << std::endl;
        // TODO: unify this
        if (auto builtin = get_builtin(n)) {
             // std::cout << "extern fn" << n << std::endl;
             extern_fns.push_back(builtin.value());
        } else if (auto i = get_vm_builtin_cases_idx(env, n)) {
             auto arity = 2; // get_vm_builtin_cases()
             extern_fns.push_back(mk_lean_extern(n, arity));
        } else {
            extern_fns.push_back(mk_extern(n, 0));
        }
    });

    // Finally we assert that there are no more unprocessed declarations.
    lean_assert(used_names.stack_is_empty());

    native_compile(env, conf, extern_fns, all_procs, native_compiler_mode::JIT);
}

void native_compile_binary(environment const & env, config & conf, declaration const & d) {
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
        // TODO: unify this
        if (auto builtin = get_builtin(n)) {
            // std::cout << "extern fn" << n << std::endl;
            extern_fns.push_back(builtin.value());
        } else if (auto i = get_vm_builtin_cases_idx(env, n)) {
            auto arity = 2u; // FIX ME TOTAL BUG
            extern_fns.push_back(mk_lean_extern(n, arity));
        }
    });

    // Finally we assert that there are no more unprocessed declarations.
    lean_assert(used_names.stack_is_empty());

    native_compile(env, conf, extern_fns, all_procs, native_compiler_mode::AOT);
}

void initialize_native_compiler() {
    register_trace_class("native_compiler");
    register_trace_class({"native_compiler", "preprocess"});
}

void finalize_native_compiler() {
}
}
