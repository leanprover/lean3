/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "kernel/environment.h"
#include "simple_expr.h"

namespace lean  {
    struct proc {
        name m_name;
        simple_expr m_body;
        proc(name m_name, simple_expr body) : m_name(m_name), m_body(body) {}
    };

    class c_backend {
        environment const & m_env;
        std::vector<proc> m_procs;
    public:
        c_backend(environment const & env, optional<std::string> main_fn);
        simple_expr compile_expr(expr const & e);
        simple_expr compile_expr(expr const & e, std::vector<binding> & bindings);
        simple_expr compile_expr_app(expr const & e, std::vector<binding> & bindings);
        simple_expr compile_error(std::string s);
        void compile_decl(declaration const & d);
        void add_proc(proc p);
    };
}
