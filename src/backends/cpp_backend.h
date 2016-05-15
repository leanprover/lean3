/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "kernel/environment.h"
#include "backend.h"
#include "clike_backend.h"
#include "c_emitter.h"
#include "simple_expr.h"

namespace lean  {
    class cpp_backend : public clike_backend {
        bool m_return;
    public:
        cpp_backend(environment const & env, config & conf);
        virtual void generate_includes(std::ostream& os);
        virtual void generate_main(std::ostream& os, std::string main_fn);
        virtual void generate_proc(std::ostream& os, proc const & p);
        virtual void generate_decl(std::ostream& os, proc const & p);
        virtual void generate_ctor(std::ostream& os, ctor const & c);
        virtual void generate_binding(std::ostream& os, pair<name, shared_ptr<simple_expr>> & p);
        virtual void generate_simple_expr_let(std::ostream& os, simple_expr const & se);
        virtual void generate_simple_expr_switch(std::ostream& os, simple_expr const & se);
        virtual void generate_simple_expr_call(std::ostream& os, simple_expr const & se);
        virtual void generate_simple_expr_error(std::ostream& os, simple_expr const & se);
        virtual void generate_simple_expr_var(std::ostream& os, simple_expr const & se);
        virtual void generate_simple_expr_project(std::ostream& os, simple_expr const & se);
        virtual void generate_simple_expr_closure_alloc(std::ostream& os, simple_expr const & se);
    };
}
