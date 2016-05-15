/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "backend_exception.h"
#include "simple_expr.h"
#include "config.h"

namespace lean  {
    using std::shared_ptr;

    struct ctor {
        int m_ctor_index;
        name m_name;
        int m_arity;
        
        ctor(int m_ctor_index, name m_name, int m_arity)
            : m_ctor_index(m_ctor_index), m_name(m_name), m_arity(m_arity) {}
    };

    struct proc {
        name m_name;
        std::vector<name> m_args;
        shared_ptr<simple_expr> m_body;
        int m_arity;

        proc(name m_name, std::vector<name> args, shared_ptr<simple_expr> body)
            : m_name(m_name), m_args(args), m_body(body) {
                m_arity = args.size();
            }
        proc() : m_name(), m_args(), m_body(nullptr), m_arity(0) {}
        int arity() const { return m_arity; }
    };

    // Represents a code generation backend
    class backend {
    protected:
        environment const & m_env;
        type_checker m_tc;
        name_map<proc> m_procs;
        // TODO: convert this to be a map as well.
        std::vector<ctor> m_ctors;
        bool m_debug_tracing;
        config & m_conf;
    public:
        backend(environment const & env, config & conf);
        // This inteface is used for lowering core expressions down to
        // the simplified ANF, closure converted language for used for
        // code generation.
        shared_ptr<simple_expr> compile_body(std::vector<name> & args, expr const & e);
        shared_ptr<simple_expr> compile_expr(expr const & e);
        shared_ptr<simple_expr> compile_expr(expr const & e, std::vector<binding> & bindings);
        shared_ptr<simple_expr> compile_expr_lambda(expr const & e, std::vector<binding> & bindings);
        shared_ptr<simple_expr> compile_expr_macro(expr const & e, std::vector<binding> & bindings);
        shared_ptr<simple_expr> compile_expr_app(expr const & e, std::vector<binding> & bindings);
        // This is hack, thought we could just use kernel let bindings, but
        // the front-end still produces macros.
        shared_ptr<simple_expr> compile_expr_let_impl(
            name const & n,
            expr const & value,
            expr const & body,
            std::vector<binding> & bindings);
        shared_ptr<simple_expr> compile_expr_let(expr const & e, std::vector<binding> & bindings);
        shared_ptr<simple_expr> compile_expr_const(expr const & e);
        shared_ptr<simple_expr> compile_expr_local(expr const & e);
        // Generate a procedure corresponding to the recursor.
        void compile_recursor(expr const & e);
        shared_ptr<simple_expr> compile_error(std::string s);

        // The code generator interface, to add a new backend simply subclass
        // this type and declare this methods.
        virtual void generate_code() = 0;

        // Utility methods for interacting with the state encapsulated by this
        // object.
        void bind_name(name n, expr const & e, std::vector<binding> & bindings);
        void compile_decl(declaration const & d);
        void compile_intro_rule(declaration const & d);
        void add_proc(proc p);
        name fresh_name();
        name fresh_name_with_prefix(name const & prefix);
    };

    shared_ptr<simple_expr> let_binding(std::vector<binding> bindings, shared_ptr<simple_expr> se);
}
