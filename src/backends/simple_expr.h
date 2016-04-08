/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "kernel/environment.h"

namespace lean  {
    struct simple_expr {
        friend std::ostream& operator<<(std::ostream& os, const simple_expr & e);
        void display(std::ostream& os) const;
    };

    typedef pair<name, simple_expr> binding;

    struct simple_expr_var : simple_expr {
        name m_name;
        simple_expr_var(name m_name) : m_name(m_name) {}
    };

    struct simple_expr_let : simple_expr {
        std::vector<std::pair<name, simple_expr>> m_name;
        simple_expr m_body;
    };

    struct simple_expr_call : simple_expr {
        name m_name;
        std::vector<simple_expr> m_args;
    };

    struct simple_expr_error : simple_expr {
        std::string m_error_msg;
        simple_expr_error(std::string msg) : m_error_msg(msg) {}
    };
}
