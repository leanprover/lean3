/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "kernel/environment.h"
#include "backend.h"
#include "c_emitter.h"
#include "simple_expr.h"

namespace lean  {
    void mangle_name(std::ostream& os, name const & n);
    void mangle_name_fn_ptr(std::ostream& os, name const & n);
    // A helper class for backend's that generate code similar to C,
    // for example a C, CPP, Go, or Rust backend would ideally use this.
    class clike_backend : public backend {
        bool m_return;
    public:
        clike_backend(environment const & env, config & conf);
        virtual void generate_code();
        virtual void generate_main(std::ostream& os, std::string main_fn) = 0;
        virtual void generate_includes(std::ostream& os) = 0;
        virtual void generate_proc(std::ostream& os, proc const & p) = 0;
        virtual void generate_decl(std::ostream& os, proc const & p) = 0;
        virtual void generate_simple_expr(std::ostream& os, simple_expr const & se);
        virtual void generate_ctor(std::ostream& os, ctor const & c) = 0;
        virtual void generate_binding(std::ostream& os, pair<name, shared_ptr<simple_expr>> & p) = 0;
        virtual void generate_simple_expr_let(std::ostream& os, simple_expr const & se) = 0;
        virtual void generate_simple_expr_switch(std::ostream& os, simple_expr const & se) = 0;
        virtual void generate_simple_expr_call(std::ostream& os, simple_expr const & se) = 0;
        virtual void generate_simple_expr_error(std::ostream& os, simple_expr const & se) = 0;
        virtual void generate_simple_expr_var(std::ostream& os, simple_expr const & se) = 0;
        virtual void generate_simple_expr_project(std::ostream& os, simple_expr const & se) = 0;
        virtual void generate_simple_expr_closure_alloc(std::ostream& os, simple_expr const & se) = 0;
    };
}
