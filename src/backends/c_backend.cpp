    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <iostream>
#include <utility>
#include "c_backend.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {

void print_decl(environment const & env, declaration const & d) {
    if (d.is_axiom()) {
        std::cout << "axiom: " << std::endl;
        std::cout << d.get_name() << std::endl;
    } else if (d.is_definition()) {
        std::cout << "def: "
        << d.get_name()
        << " : " << d.get_type() << " := "
        << d.get_value() << std::endl;
    } else if (d.is_constant_assumption()) {
        // bool is_definition() const;
        // bool is_axiom() const;
        // bool is_theorem() const;
        // bool is_constant_assumption() const;

        std::cout << "constant assumption: " << std::endl;
        std::cout << d.get_name() << " : " << d.get_type() << std::endl;
        bool is_inductive;

        if (inductive::is_intro_rule(env, d.get_name())) {
            is_inductive = true;
        } else {
            is_inductive = false;
        }
        std::cout << is_inductive << std::endl;

    } else if (d.is_theorem()) {
        std::cout << "theorem" << std::endl;
    }
}

struct used_defs {
    name_set m_used_names;
    std::vector<name> m_names_to_process;
    environment const & m_env;
    // Need a stack and a HashSet
    // Rough algorithm
    // For each name, check to see if its
    // in the set, if not push it on to the stack,
    // when done processing the main fucntion,
    // invoke this procedure with the first item
    // from the stack, and repeat until the stack
    // is empty.
    used_defs(environment const & env);
    void names_in_decl(declaration const & d);
    void names_in_expr(expr const & e);
    void add_name(name const & n);
};

used_defs::used_defs(environment const & env) : m_env(env) {
    this->m_used_names = name_set();
    this->m_names_to_process = std::vector<name>();
}

// Add a name to the live name set, marking
// marking it as seen, and queuing it to be processed.
void used_defs::add_name(name const & n) {
    if (!this->m_used_names.contains(n)) {
        this->m_used_names.insert(n);
        this->m_names_to_process.push_back(n);
    }
}

void used_defs::names_in_decl(declaration const & d) {
    auto n = d.get_name();

    // Start with the name of the current decl,
    // we then will collect, the set of names in
    // the body, and push them on to the stack to
    // be processed, we will repeat this until,
    // the stack is empty.
    this->add_name(n);

    if (d.is_definition()) {
        // Get the names from the body.
        auto body = d.get_value();
        this->names_in_expr(body);
    }

    // Finally we need to recursively process the
    // remaining definitions to full compute the
    // working set.
    while (!this->m_names_to_process.empty()) {
        auto n = this->m_names_to_process.back();
        this->m_names_to_process.pop_back();
        this->names_in_decl(this->m_env.get(n));
    }

    lean_assert(this->m_names_to_process.empty());
}

void used_defs::names_in_expr(expr const & e) {
    std::cout << "exp: " << e << std::endl;
    switch (e.kind()) {
        case expr_kind::Local: case expr_kind::Meta:
            break;
        case expr_kind::Var:
            std::cout << "var: " << e << std::endl;
            break;
        case expr_kind::Sort:
            break;
        case expr_kind::Constant:
            this->add_name(const_name(e));
            break;
        case expr_kind::Macro:
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            this->names_in_expr(binding_domain(e));
            this->names_in_expr(binding_body(e));
            break;
        case expr_kind::App:
            this->names_in_expr(app_fn(e));
            this->names_in_expr(app_arg(e));
        case expr_kind::Let:
            break;
    }
}

c_backend::c_backend(environment const & env, optional<std::string> main_fn)
    : m_env(env) {
    auto main_name = name(main_fn.value());
    auto main = env.get(main_name);
    print_decl(env, main);
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

void c_backend::compile_decl(declaration const & d) {
    auto name = d.get_name();
    if (d.is_axiom()) {
        std::cout << "axiom: " << std::endl;
        std::cout << d.get_name() << std::endl;
    } else if (d.is_definition()) {
        auto ty = d.get_type();
        auto value = d.get_value();

        auto se = this->compile_expr(value);
        // return proc(name, se);
    } else if (d.is_constant_assumption()) {
        std::cout << "constant assumption: " << std::endl;
        std::cout << d.get_name() << " : " << d.get_type() << std::endl;
        bool is_inductive;

        if (inductive::is_intro_rule(this->m_env, d.get_name())) {
            is_inductive = true;
        } else {
            is_inductive = false;
        }
        std::cout << is_inductive << std::endl;
    } else if (d.is_theorem()) {
        std::cout << "theorem" << std::endl;
    } else {
        std::cout << "unhandled case" << name << std::endl;

    }
}

simple_expr c_backend::compile_expr(expr const & e) {
    std::vector<pair<name, simple_expr>> bindings;
    auto simpl_expr = compile_expr(e, bindings);
    for (auto binding : bindings) {
        std::cout << binding.first << " : " << binding.second << std::endl;
    }
    return simple_error_expr(std::string("unable to execute this expression"));
}

simple_expr c_backend::compile_expr(expr const & e, std::vector<binding> & bindings) {
    std::cout << "exp: " << e << std::endl;
    switch (e.kind()) {
        case expr_kind::Local: case expr_kind::Meta:
            std::cout << "local/meta: not supported" << std::endl;
            break;
        case expr_kind::Var:
            std::cout<< "var: not supported" << std::endl;
            break;
        case expr_kind::Sort:
            std::cout<< "sort: not supported" << std::endl;
            break;
        case expr_kind::Constant:
            std::cout<< "constant: not supported" << std::endl;
            break;
        case expr_kind::Macro:
            std::cout<< "macro: not supported" << std::endl;
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            std::cout<< "pi: not supported" << std::endl;
            break;
        case expr_kind::App:
            return compile_expr_app(e, bindings);
            break;
        case expr_kind::Let:
            break;
    }
    throw new std::string("app: not supported");
}

simple_expr c_backend::compile_expr_const(expr const & e, std::vector<binding> & bindings) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    unsigned nargs = args.size();``
    for (unsigned i = 0; i < nargs; i++) {
         std::cout << args[i] << std::endl;
    }
}

simple_expr c_backend::compile_expr_app(expr const & e, std::vector<binding> & bindings) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    unsigned nargs = args.size();
    for (unsigned i = 0; i < nargs; i++) {
         std::cout << args[i] << std::endl;
    }

}

simple_expr c_backend::compile_error(std::string s) {
    throw "a";
}

void c_backend::add_proc(proc p) {
    this->m_procs.push_back(p);
}

}
