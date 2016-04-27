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
    class c_backend : backend {
        c_emitter m_emitter;
        bool m_return;
    public:
        c_backend(environment const & env, optional<std::string> main_fn);
        virtual void generate_code(optional<std::string> output_path);
        virtual void generate_proc(std::ostream& os, proc const & p);
        void generate_decl(std::ostream& os, proc const & p);
        virtual void generate_simple_expr(std::ostream& os, simple_expr const & se);
        void generate_ctor(std::ostream& os, ctor const & c);
        void generate_binding(std::ostream& os, pair<name, shared_ptr<simple_expr>> & p);
        void generate_simple_expr_let(std::ostream& os, simple_expr const & se);
        void generate_simple_expr_switch(std::ostream& os, simple_expr const & se);
        void generate_simple_expr_call(std::ostream& os, simple_expr const & se);
        void generate_simple_expr_error(std::ostream& os, simple_expr const & se);
        void generate_simple_expr_var(std::ostream& os, simple_expr const & se);
    };
}
