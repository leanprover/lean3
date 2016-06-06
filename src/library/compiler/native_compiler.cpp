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
    bool m_emit_return;

    expr mk_local(name const & n) {
        return ::lean::mk_local(n, mk_neutral_expr());
    }
    //
    // void compile_args(unsigned nargs, expr const * args, unsigned bpz, name_map<unsigned> const & m) {
    //     for (unsigned i = 0; i < nargs; i++, bpz++) {
    //         compile(args[i], bpz, m);
    //     }
    // }
    //
    // void compile_rev_args(unsigned nargs, expr const * args, unsigned bpz, name_map<unsigned> const & m) {
    //     unsigned i = nargs;
    //     while (i > 0) {
    //         --i;
    //         compile(args[i], bpz, m);
    //         bpz++;
    //     }
    // }
    //
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

    // void emit_apply_instr(unsigned n) {
    //     for (unsigned i = 0; i < n; i++)
    //         emit(mk_apply_instr());
    // }
    //

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
        } else if (optional<vm_decl> decl = get_vm_decl(m_env, n)) {
            compile_global(*decl, 0, nullptr, 0, name_map<unsigned>());
        } else {
            throw_unknown_constant(n);
        }
    }
    //
    void compile_local(expr const & e, name_map<unsigned> const & m) {
        unsigned idx = *m.find(mlocal_name(e));
        this->m_emitter.emit_local(idx);
    }

    void compile_cases_on(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        // buffer<expr> args;
        // expr fn = get_app_args(e, args);
        // lean_assert(is_constant(fn));
        // name const & fn_name = const_name(fn);
        // unsigned num;
        // if (fn_name == get_nat_cases_on_name()) {
        //     num = 2;
        // } else {
        //     lean_assert(is_internal_cases(fn));
        //     num = *is_internal_cases(fn);
        // }
        // lean_assert(args.size() == num + 1);
        // lean_assert(num >= 1);
        // /** compile major premise */
        // compile(args[0], bpz, m);
        // unsigned cases_pos = next_pc();
        // buffer<unsigned> cases_args;
        // buffer<unsigned> goto_pcs;
        // cases_args.resize(num, 0);
        // if (fn_name == get_nat_cases_on_name())
        //     emit(mk_nat_cases_instr(0, 0));
        // else if (num == 1)
        //     emit(mk_destruct_instr());
        // else if (num == 2)
        //     emit(mk_cases2_instr(0, 0));
        // else
        //     emit(mk_casesn_instr(cases_args.size(), cases_args.data()));
        // for (unsigned i = 1; i < args.size(); i++) {
        //     cases_args[i - 1] = next_pc();
        //     expr b = args[i];
        //     buffer<expr> locals;
        //     name_map<unsigned> new_m = m;
        //     unsigned new_bpz = bpz;
        //     while (is_lambda(b)) {
        //         name n = mk_fresh_name();
        //         new_m.insert(n, new_bpz);
        //         locals.push_back(mk_local(n));
        //         new_bpz++;
        //         b = binding_body(b);
        //     }
        //     b = instantiate_rev(b, locals.size(), locals.data());
        //     compile(b, new_bpz, new_m);
        //     if (locals.size() > 0)
        //         emit(mk_drop_instr(locals.size()));
        //     // if it is not the last case, we need to use a goto
        //     if (i + 1 < args.size()) {
        //         goto_pcs.push_back(next_pc());
        //         emit(mk_goto_instr(0)); // fix later
        //     }
        // }
        // /* Fix cases instruction pc's */
        // if (num >= 2) {
        //     for (unsigned i = 0; i < cases_args.size(); i++)
        //         m_code[cases_pos].set_pc(i, cases_args[i]);
        // }
        // unsigned end_pc = next_pc();
        // /* Fix goto instruction pc's */
        // for (unsigned i = 0; i < goto_pcs.size(); i++) {
        //     m_code[goto_pcs[i]].set_goto_pc(end_pc);
        // }
    }

    void compile_cnstr(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        // buffer<expr> args;
        // expr const & fn = get_app_args(e, args);
        // lean_assert(is_internal_cnstr(fn));
        // unsigned cidx = *is_internal_cnstr(fn);
        // compile_args(args.size(), args.data(), bpz, m);
        // emit(mk_constructor_instr(cidx, get_app_num_args(e)));
        throw exception("NYI constructor");
    }


    void compile_proj(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_internal_proj(fn));
        unsigned idx = *is_internal_proj(fn);

        this->m_emitter.emit_projection(idx);
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
            // compile_rev_args(args.size(), args.data(), bpz+1, m);
            // compile(fn, bpz, m);
            // emit_apply_instr(args.size());
            throw exception("NYI call");
            return;
        } else if (is_constant(fn)) {
            if (auto n = get_vm_builtin_internal_name(const_name(fn))) {
                std::string s("lean::");
                s += n;
                auto nm = name(s);
                this->m_emitter.emit_c_call(nm, args.size(), args.data(), [=] (expr const & e) {
                    compile(e, bpz, m);
                });
            } else if (is_neutral_expr(fn)) {
                // emit(mk_sconstructor_instr(0));
                throw exception("NYI call");
            } else if (optional<vm_decl> decl = get_vm_decl(m_env, const_name(fn))) {
                compile_global(*decl, args.size(), args.data(), bpz, m);
            } else {
                throw_unknown_constant(const_name(fn));
            }
        } else {
            lean_unreachable();
        }
    }

    void compile_app(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        expr const & fn = get_app_fn(e);
        if (is_internal_cases(fn) || is_constant(fn, get_nat_cases_on_name())) {
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
        for (auto fn : fns) {
            this->m_emitter.emit_prototype(fn.first, fn.second);
        }
    }

    void operator()(name const & n, expr e) {
        this->m_emitter.emit_decl(n, e, [=] (expr e) {
            // This is temporary hack, better way would be to annotate all
            // terminating cf branches.
            m_emit_return = true;
            buffer<expr> locals;
            unsigned bpz   = 0;
            unsigned arity = get_arity(e);
            unsigned i     = arity;
            name_map<unsigned> m;
            while (is_lambda(e)) {
                name n = mk_fresh_name();
                i--;
                m.insert(n, i);
                locals.push_back(mk_local(n));
                bpz++;
                e = binding_body(e);
            }
            e = instantiate_rev(e, locals.size(), locals.data());
            if (this->m_emit_return) {
                this->m_emitter.emit_return([&] () {
                    compile(e, bpz, m);
                });
            } else {
                compile(e, bpz, m);
            }
        });
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

    // Iterate each processed decl, emitting code for it.
    for (auto & p : procs) {
        lean_trace(name({"native_compiler"}), tout() << "" << p.first << "\n";);
        name & n = p.first;
        expr body = p.second;
        compiler(n, body);
    }

    compiler.emit_main();
}

void native_compile(environment const & env, config & conf, declaration const & d, native_compiler_mode mode) {
    lean_trace(name({"native_compiler"}),
        tout() << "main_fn: " << d.get_name() << "\n";);

    lean_trace(name({"native_compiler"}),
        tout() << "main_body: " << d.get_value() << "\n";);

    // Preprocess the main function.
    buffer<pair<name, expr>> main_procs;
    preprocess(env, d, main_procs);

    if (mode == native_compiler_mode::AOT) {
        // Compute the live set of names, for each resulting proc.
        used_defs used_names(env);
        for (auto pair : main_procs) {
            used_names.names_in_expr(pair.second);
        }

        // Collect the remaining live declarations.
        auto decls_to_compile = std::vector<declaration>();
        used_names.m_used_names.for_each([&] (name const &n) {
            decls_to_compile.push_back(env.get(n));
        });

        // Collect all the generated procs.
        buffer<pair<name, expr>> all_procs;
        buffer<pair<name, unsigned>> extern_fns;

        for (auto decl : decls_to_compile) {
            std::cout << "preproces:" << decl.get_name() << std::endl;
            // if (is_extern(env, decl.get_name())) {
            //     std::cout << "extern: " << std::endl;
            //     std::cout << decl.get_name() << std::endl;
            // } else

            if (decl.is_definition()) {
                std::cout << "preprocess_body:" << decl.get_value() << std::endl;

                buffer<pair<name, expr>> procs;
                preprocess(env, decl, procs);

                for (auto p : procs) {
                    all_procs.push_back(p);
                }
            } else if (decl.is_constant_assumption()) {
                // We handle introduction rules, externs, and builtins specially.
                if (auto n = inductive::is_intro_rule(env, decl.get_name())) {
                    //compile_intro_rule(d);
                } else if (is_extern(env, decl.get_name())) {
                    std::cout << "extern: " << decl.get_name() << std::endl;
                } else if (auto n = get_vm_builtin_internal_name(decl.get_name())) {
                    auto arity = get_vm_builtin_arity(decl.get_name());
                    extern_fns.push_back(pair<name, unsigned>(n, arity));
                }
            }
        }

        // Remember to add back the ones from main.
        for (auto p : main_procs) {
            all_procs.push_back(p);
        }

        native_compile(env, conf, extern_fns, all_procs);
    } else {
        buffer<pair<name, unsigned>> extern_fns;
        native_compile(env, conf, extern_fns, main_procs);
    }
}

void initialize_native_compiler() {
    register_trace_class({"native_compiler"});
}

void finalize_native_compiler() {
}
}
