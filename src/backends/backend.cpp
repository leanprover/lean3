    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <iostream>
#include <memory>
#include <tuple>
#include <utility>
#include "backend.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "used_names.h"
#include "util/fresh_name.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {

// void print_decl(environment const & env, declaration const & d) {
//     if (d.is_axiom()) {
//         std::cout << "axiom: " << std::endl;
//         std::cout << d.get_name() << std::endl;
//     } else if (d.is_definition()) {
//         std::cout << "def: "
//         << d.get_name()
//         << " : " << d.get_type() << " := "
//         << d.get_value() << std::endl;
//     } else if (d.is_constant_assumption()) {
//         // bool is_definition() const;
//         // bool is_axiom() const;
//         // bool is_theorem() const;
//         // bool is_constant_assumption() const;
//
//         std::cout << "constant assumption: " << std::endl;
//         std::cout << d.get_name() << " : " << d.get_type() << std::endl;
//         bool is_inductive;
//
//         if (inductive::is_intro_rule(env, d.get_name())) {
//             is_inductive = true;
//         } else {
//             is_inductive = false;
//         }
//         std::cout << is_inductive << std::endl;
//
//     } else if (d.is_theorem()) {
//         std::cout << "theorem" << std::endl;
//     }
// }

backend::backend(environment const & env, optional<std::string> main_fn)
    : m_env(env) {
    auto main_name = name(main_fn.value());
    auto main = env.get(main_name);
    // print_decl(env, main);
    used_defs used_names(env);
    used_names.names_in_decl(main);
    std::cout << "-----------debug---------------" << main_fn.value() << std::endl;
    auto decls_to_compile = std::vector<declaration>();
    used_names.m_used_names.for_each([&] (name const &n) {
        decls_to_compile.push_back(env.get(n));
    });

    for (auto decl : decls_to_compile) {
        this->compile_decl(decl);
        //print_decl(env, decl);
    }
}

void backend::compile_decl(declaration const & d) {
    if (d.is_axiom()) {
        std::cout << "axiom: " << std::endl;
        std::cout << d.get_name() << std::endl;
    } else if (d.is_definition()) {
        auto ty = d.get_type();
        auto value = d.get_value();

        std::vector<name> args;
        auto se = this->compile_body(args, value);
        auto p = proc(d.get_name(), args, se);
        this->add_proc(p);
    } else if (d.is_constant_assumption()) {
        if (auto n = inductive::is_intro_rule(this->m_env, d.get_name())) {
            auto tup = inductive::is_inductive_decl(this->m_env, n.value());
            if (tup) {
                auto inductive_types = std::get<2>(tup.value());
                inductive::inductive_decl ind_ty;
                for (auto it : inductive_types) {
                    if (n.value() == inductive::inductive_decl_name(it)) {
                      ind_ty = it;
                    }
                }

                auto intro_rules = inductive::inductive_decl_intros(ind_ty);

                int ctor_index = -1;
                int arity = 0;

                int i = 0;
                for (auto intro : intro_rules) {
                      std::cout << "intro_rule: " << intro << std::endl;
                      std::cout << "kind: " << intro.kind() << std::endl;
                      auto intro_n = inductive::intro_rule_name(intro);
                      auto intro_ty = inductive::intro_rule_type(intro);
                      std::cout << "type: " << intro_ty << std::endl;

                      if (intro_n == d.get_name()) {
                          ctor_index = i;
                          while (is_pi(intro_ty)) {
                              arity += 1;
                              intro_ty = binding_body(intro_ty);
                          }
                          break;
                      }

                      i += 1;
                }

                std::cout << "inductive type " << n.value() << std::endl;
                this->m_ctors.push_back(ctor(ctor_index, d.get_name(), arity));
            } else {
                throw "don't work";
            }
        } else {
            std::cout << "unhandled constant assumption: " << std::endl;
        }
    } else if (d.is_theorem()) {
        std::cout << "theorem" << std::endl;
    } else {
        std::cout << "unhandled case" << d.get_name() << std::endl;

    }
}

shared_ptr<simple_expr> backend::compile_body(std::vector<name> & args, expr const & e) {
    if (is_lambda(e)) {
        buffer<expr> ls;
        auto ex = e;
        while (is_binding(ex)) {
            expr d = instantiate_rev(binding_domain(ex), ls.size(), ls.data());
            auto n = mk_fresh_name(); // (name const & prefix, unsigned k);
            expr l = mk_local(n, binding_name(ex), d, binding_info(ex));
            args.push_back(n);
            ls.push_back(l);
            ex = binding_body(ex);
        }
        ex = instantiate_rev(ex, ls.size(), ls.data());
        return this->compile_expr(ex);
    } else {
        return this->compile_expr(e);
    }
}

shared_ptr<simple_expr> backend::compile_expr(expr const & e) {
    std::vector<binding> bindings;
    auto se = compile_expr(e, bindings);
    for (auto binding : bindings) {
        std::cout << binding.first << " : " << binding.second << std::endl;
    }

    return let_binding(bindings, se);
}

shared_ptr<simple_expr> backend::compile_expr(expr const & e, std::vector<binding> & bindings) {
    std::cout << "exp: " << e << std::endl;
    switch (e.kind()) {
        case expr_kind::Local:
            return shared_ptr<simple_expr>(new simple_expr_error("local"));
        case expr_kind::Meta:
            std::cout << "meta: not supported" << std::endl;
            break;
        case expr_kind::Var:
            std::cout<< "var: not supported" << std::endl;
            break;
        case expr_kind::Sort:
            std::cout<< "sort: not supported" << std::endl;
            break;
        case expr_kind::Constant:
            return this->compile_expr_const(e);
        case expr_kind::Macro:
            return this->compile_expr_macro(e, bindings);
        case expr_kind::Lambda:
            return this->compile_expr_lambda(e, bindings);
        case expr_kind::Pi:
            std::cout<< "pi: not supported" << std::endl;
            break;
        case expr_kind::App:
            return this->compile_expr_app(e, bindings);
        case expr_kind::Let:
            break;
    }
    throw new std::string("app: not supported");
}

shared_ptr<simple_expr> backend::compile_expr_const(expr const & e) {
    name n = name(const_name(e));
    return shared_ptr<simple_expr>(new simple_expr_var(n));
}

shared_ptr<simple_expr> backend::compile_expr_app(expr const & e, std::vector<binding> & bindings) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    unsigned nargs = args.size();
    std::vector<name> names;
    for (unsigned i = 0; i < nargs; i++) {
         std::cout << args[i] << std::endl;
         auto n = mk_fresh_name();
         this->bind_name(n, args[i], bindings);
         names.push_back(n);
    }

    if (is_constant(f)) {
        auto callee_name = const_name(f);
        return shared_ptr<simple_expr>(new simple_expr_call(callee_name, names, 1));
    } else {
        auto callee_name = mk_fresh_name();
        this->bind_name(callee_name, f, bindings);
        return shared_ptr<simple_expr>(new simple_expr_call(callee_name, names));
    }
}

shared_ptr<simple_expr> backend::compile_expr_macro(expr const & e, std::vector<binding> & bindings) {
    auto def = macro_def(e);
    std::cout << "macro: not supported(";
    def.display(std::cout);
    std::cout << ")" << std::endl;
    return shared_ptr<simple_expr>(new simple_expr_error(std::string("macro_here")));
}

shared_ptr<simple_expr> backend::compile_expr_lambda(expr const & e, std::vector<binding> & bindings) {
    return shared_ptr<simple_expr>(new simple_expr_error(std::string("macro_here")));
}


shared_ptr<simple_expr> backend::compile_error(std::string msg) {
    return shared_ptr<simple_expr>(new simple_expr_error(msg));
}

void backend::bind_name(name n, expr const & e, std::vector<binding> & bindings) {
    auto simple_arg = this->compile_expr(e, bindings);
    bindings.push_back(binding(n, simple_arg));
}

void backend::add_proc(proc p) {
    this->m_procs.push_back(p);
}

shared_ptr<simple_expr> let_binding(std::vector<binding> bindings, shared_ptr<simple_expr> se) {
    if (bindings.empty()) {
        return se;
    } else {
        return std::shared_ptr<simple_expr>(new simple_expr_let(bindings, se));
    }
}

}
