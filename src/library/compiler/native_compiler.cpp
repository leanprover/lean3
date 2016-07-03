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
#include "library/util.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/nat_value.h"
#include "library/compiler/preprocess.h"
#include "library/compiler/native_compiler.h"
#include "library/compiler/annotate_return.h"
#include "library/compiler/anf_transform.h"
#include "config.h"
#include "cpp_emitter.h"
#include "used_names.h"
#include "library/extern.h"
#include "library/vm/vm.h"

namespace lean {
class native_compiler_fn {
    environment        m_env;
    config & m_conf;
    cpp_emitter m_emitter;

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
        } else {
            this->m_emitter.mangle_name(n);
        }
        // } else if (optional<vm_decl> decl = get_vm_decl(m_env, n)) {
        //     compile_global(*decl, 0, nullptr, 0, name_map<unsigned>());
        // } else {
        //     throw_unknown_constant(n);
        // }
    }

    void compile_local(expr const & e, name_map<unsigned> const & m) {
        std::cout << mlocal_name(e) << std::endl;
        m.for_each([&] (name const & n, unsigned const & i) {
            std::cout << n << " ======> " << i << std::endl;
        });
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
        } else {
            lean_assert(is_internal_cases(fn));
            num = *is_internal_cases(fn);
        }

        lean_assert(args.size() == num + 1);
        lean_assert(num >= 1);

        if (fn_name == get_nat_cases_on_name()) {
            this->m_emitter.emit_nat_cases(args[0], args[1], args[2], [&] (expr const & e) {
                expr b = e;
                buffer<expr> locals;
                name_map<unsigned> new_m = m;
                unsigned new_bpz = bpz;
                while (is_lambda(b)) {
                    name n = mk_fresh_name();
                    std::cout << "making new name" << std::endl;
                    new_m.insert(n, new_bpz);
                    locals.push_back(mk_local(n));
                    new_bpz++;
                    b = binding_body(b);
                }
                b = instantiate_rev(b, locals.size(), locals.data());
                compile(b, new_bpz, new_m);
            });
        } else {
            this->m_emitter.emit_cases_on(name("scrut"), args, [&] (expr & b) {
                buffer<expr> locals;
                name_map<unsigned> new_m = m;
                unsigned new_bpz = bpz;
                while (is_lambda(b)) {
                    name n = mk_fresh_name();
                    new_m.insert(n, new_bpz);
                    locals.push_back(mk_local(n));
                    new_bpz++;
                    b = binding_body(b);
                }
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

        this->m_emitter.emit_projection(idx); // args.size() - 1, args.data() + 1);
        // lean_assert(args.size() >= 1);
        // compile_rev_args(args.size() - 1, args.data() + 1, bpz, m);
        // bpz += args.size() - 1;
        // compile(args[0], bpz, m);
        // emit(mk_proj_instr(idx));
        // emit_apply_instr(args.size() - 1);
        // throw exception("NYI projection");
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
                std::string s("lean::");
                s += n;
                auto nm = name(s);
                this->m_emitter.emit_c_call(nm, args.size(), args.data(), [=] (expr const & e) {
                    compile(e, bpz, m);
                });
            } else if (is_neutral_expr(fn)) {
                this->m_emitter.emit_sconstructor(0);
            } else if (optional<vm_decl> decl = get_vm_decl(m_env, const_name(fn))) {
                compile_global(*decl, args.size(), args.data(), bpz, m);
            } else {
                this->m_emitter.emit_c_call(
                    const_name(fn),
                    args.size(),
                    args.data(), [=] (expr const & e) {});
                // Not sure how to do this correctly?
                // throw_unknown_constant(const_name(fn));
            }
        } else {
            lean_unreachable();
        }
    }

    void compile_app(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        expr const & fn = get_app_fn(e);
        std::cout << "compile_app: " << fn << std::endl;

        if (is_return_expr(fn)) {
            auto arg = app_arg(e);
            this->m_emitter.emit_return([&] () {
                compile(arg, bpz, m);
            });
        } else if (is_internal_cases(fn) || is_constant(fn, get_nat_cases_on_name())) {
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
            std::cout << value << std::endl;
            this->m_emitter.emit_mpz((get_nat_value_value(e)));
        } else if (is_annotation(e)) {
            compile(get_annotation_arg(e), bpz, m);
        } else {
            throw exception(sstream() << "code generation failed, unexpected kind of macro has been found: '"
                            << macro_def(e).get_name() << "'");
        }
    }

    void compile(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
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
    native_compiler_fn(environment const & env, config & conf):
        m_env(env), m_conf(conf), m_emitter(cpp_emitter(std::string("out.cpp"))) {}

    void emit_headers() {
        this->m_emitter.emit_headers();
    }

    void emit_main() {
        name main_fn(this->m_conf.m_main_fn);
        this->m_emitter.emit_main(main_fn);
    }

    void emit_prototypes(buffer<pair<name, unsigned>> fns) {

        this->m_emitter.emit_string("namespace lean {\n");
        for (auto fn : fns) {
            this->m_emitter.emit_prototype(fn.first, fn.second);
        }
        this->m_emitter.emit_string("}\n");
    }

    void operator()(name const & n, expr e) {
        // This is temporary hack, better way would be to annotate all
        // terminating cf branches.
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
};

void native_compile(environment const & env,
                    config & conf,
                    buffer<pair<name, unsigned>> & extern_fns,
                    buffer<pair<name, expr>> & procs) {
    native_compiler_fn compiler(env, conf);

    // Emit the header includes.
    compiler.emit_headers();

    // Emit externs (currently only works for builtins).
    compiler.emit_prototypes(extern_fns);

    for (auto & p : procs) {
        compiler.emit_prototype(p.first, p.second);
    }

    // Iterate each processed decl, emitting code for it.
    for (auto & p : procs) {
        lean_trace(name({"native_compiler"}), tout() << "" << p.first << "\n";);
        name & n = p.first;
        expr body = p.second;
        std::cout << body << std::endl;
        compiler(n, body);
    }

    compiler.emit_main();
}

void native_preprocess(environment const & env, declaration const & d, buffer<pair<name, expr>> & procs) {
    buffer<pair<name, expr>> raw_procs;
    // Run the normal preprocessing and optimizations.
    preprocess(env, d, raw_procs);

    // Run the native specific optimizations.
    for (auto proc : raw_procs) {
        // std::cout << "native preproc" << std::endl;
        // std::cout << proc.second << std::endl;
        auto anf_body = anf_transform(env, proc.second);
        // std::cout << anf_body << std::endl;
        auto annotated_body = annotate_return(env, anf_body);
        // std::cout << annotated_body << std::endl;
        pair<name, expr> p = pair<name, expr>(proc.first, annotated_body);
        procs.push_back(p);
    }
}

// void is_extern_function(expr & e) {
//
// }

bool is_internal_decl(declaration & d) {
    auto n = d.get_name();
    return (n == name("_neutral_") ||
            n == name({"native_compiler", "return"}) ||
            is_internal_cnstr(mk_constant(n)) ||
            is_internal_cases(mk_constant(n)) ||
            is_internal_proj(mk_constant(n)));
}

optional<pair<name, unsigned>> get_builtin(name const & n) {
    auto internal_name = get_vm_builtin_internal_name(n);
    if (internal_name && get_vm_builtin_kind(n) == vm_builtin_kind::CFun) {
        auto arity = get_vm_builtin_arity(n);
        return optional<pair<name, unsigned>>(
            pair<name, unsigned>(internal_name, arity));
    } else {
        return optional<pair<name, unsigned>>();
    }
}

void native_compile(environment const & env, config & conf, declaration const & d, native_compiler_mode mode) {
    lean_trace(name("native_compiler"),
        tout() << "main_fn: " << d.get_name() << "\n";);

    lean_trace(name("native_compiler"),
        tout() << "main_body: " << d.get_value() << "\n";);

    // Preprocess the main function.
    buffer<pair<name, expr>> all_procs;
    buffer<pair<name, expr>> main_procs;
    buffer<pair<name, unsigned>> extern_fns;
    native_preprocess(env, d, main_procs);

    if (mode == native_compiler_mode::AOT) {
        // Compute the live set of names, we attach a callback that will be
        // invoked for every declaration encountered.
        used_defs used_names(env, [&] (declaration & d) {
            std::cout << "recursive processing decl" << d.get_name() << std::endl;
            buffer<pair<name, expr>> procs;
            if (is_internal_decl(d)) {
            } else if (auto p = get_builtin(d.get_name())) {
                // extern_fns.push_back(p.value());
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
                std::cout << "live constant" << n << std::endl;
            if (auto builtin = get_builtin(n)) {
                std::cout << "extern fn" << n << std::endl;
                extern_fns.push_back(builtin.value());
            }
        });

        for (auto pair : all_procs) {
            std::cout << pair.first << std::endl;
        }

        // Finally we assert that there are no more unprocessed declarations.
        lean_assert(used_names.stack_is_empty());

        native_compile(env, conf, extern_fns, all_procs);
        // // // Collect the live declarations.
        // // auto decls_to_compile = std::vector<declaration>();
        // used_names.m_used_names.for_each([&] (name const &n) {
        //     std::cout << "looking up decl: " << n << std::endl;
        //     if (n != name("_neutral_") &&
        //         n != name({"native_compiler", "return"}) &&
        //         !is_internal_cnstr(mk_constant(n))) {
        //         decls_to_compile.push_back(env.get(n));
        //     }
        // });
        //
        //

        // for (auto decl : decls_to_compile) {
        //     std::cout << "preproces:" << decl.get_name() << std::endl;
        //     // if (is_extern(env, decl.get_name())) {
        //     //     std::cout << "extern: " << std::endl;
        //     //     std::cout << decl.get_name() << std::endl;
        //     // } else
        //
        //     if (auto n = get_vm_builtin_internal_name(decl.get_name())) {
        //         auto arity = get_vm_builtin_arity(decl.get_name());
        //         extern_fns.push_back(pair<name, unsigned>(n, arity));
        //     } else if (decl.is_definition()) {
        //         std::cout << "preprocess_body:" << decl.get_value() << std::endl;
        //
        //         buffer<pair<name, expr>> procs;
        //         native_preprocess(env, decl, procs);
        //
        //         for (auto p : procs) {
        //             all_procs.push_back(p);
        //         }
        //     } else if (decl.is_constant_assumption()) {
        //         // We handle introduction rules, externs, and builtins specially.
        //         if (auto n = inductive::is_intro_rule(env, decl.get_name())) {
        //             //compile_intro_rule(d);
        //         } else if (is_extern(env, decl.get_name())) {
        //             std::cout << "extern: " << decl.get_name() << std::endl;
        //         }
        //     }
        // }
        //
        // // Remember to add back the ones from main.
        // for (auto p : main_procs) {
        //     all_procs.push_back(p);
        // }
        //
    } else {
        buffer<pair<name, unsigned>> extern_fns;
        native_compile(env, conf, extern_fns, all_procs);
    }
}

void initialize_native_compiler() {
    register_trace_class("native_compiler");
}

void finalize_native_compiler() {
}
}
