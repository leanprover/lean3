/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "simple_expr.h"

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

        proc(name m_name, std::vector<name> args, shared_ptr<simple_expr> body)
            : m_name(m_name), m_args(args), m_body(body) {}
        proc() : m_name(), m_args(), m_body(nullptr) {}
    };

    // Represents a code generation backend
    class backend {
    protected:
        environment const & m_env;
        type_checker m_tc;
        name_map<proc> m_procs;
        // TODO: convert this to be a map as well.
        std::vector<ctor> m_ctors;
    public:
        backend(environment const & env, optional<std::string> main_fn);
        // This inteface is used for lowering core expressions down to
        // the simplified ANF, closure converted language for used for
        // code generation.
        shared_ptr<simple_expr> compile_body(std::vector<name> & args, expr const & e);
        shared_ptr<simple_expr> compile_expr(expr const & e);
        shared_ptr<simple_expr> compile_expr(expr const & e, std::vector<binding> & bindings);
        shared_ptr<simple_expr> compile_expr_lambda(expr const & e, std::vector<binding> & bindings);
        shared_ptr<simple_expr> compile_expr_macro(expr const & e, std::vector<binding> & bindings);
        shared_ptr<simple_expr> compile_expr_app(expr const & e, std::vector<binding> & bindings);
        shared_ptr<simple_expr> compile_expr_const(expr const & e);
        shared_ptr<simple_expr> compile_expr_local(expr const & e);
        // Generate a procedure corresponding to the recursor.
        void compile_recursor(name const & n);
        shared_ptr<simple_expr> compile_error(std::string s);
        // The code generator interface, to add a new backend simply subclass
        // this type and declare the below methods.
        virtual void generate_code(optional<std::string> output_path) = 0;
        virtual void generate_proc(std::ostream& os, proc const & p) = 0;
        virtual void generate_simple_expr(std::ostream& os, simple_expr const & se) = 0;
        virtual void generate_binding(std::ostream& os, pair<name, shared_ptr<simple_expr>> & p) = 0;

        // Utility methods for interacting with the state encapsulated by this
        // object.
        void bind_name(name n, expr const & e, std::vector<binding> & bindings);
        void compile_decl(declaration const & d);
        void add_proc(proc p);
        name fresh_name();
        name fresh_name_with_prefix(name const & prefix);
    };

    shared_ptr<simple_expr> let_binding(std::vector<binding> bindings, shared_ptr<simple_expr> se);
}
