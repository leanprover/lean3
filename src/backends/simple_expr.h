/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include <memory>
#include "kernel/environment.h"


namespace lean  {
    using std::shared_ptr;

    enum simple_expr_kind {
        SVar,
        Let,
        Call,
        Switch,
        Error,
        Project,
        ClosureAlloc,
    };

    struct simple_expr {
        simple_expr_kind m_kind;

        virtual simple_expr_kind kind() const = 0;
        friend std::ostream& operator<<(std::ostream& os, const simple_expr & e);
        void display(std::ostream& os) const;
    };

    typedef pair<name, shared_ptr<simple_expr>> binding;

    struct simple_expr_var : simple_expr {
        name m_name;
        simple_expr_var(name m_name) : m_name(m_name) {}
        virtual simple_expr_kind kind() const { return simple_expr_kind::SVar; }
    };

    struct simple_expr_let : simple_expr {
        std::vector<binding> m_bindings;
        shared_ptr<simple_expr> m_body;
        simple_expr_let(std::vector<binding> bindings, shared_ptr<simple_expr> m_body)
            : m_bindings(bindings), m_body(m_body) {}
        virtual simple_expr_kind kind() const { return simple_expr_kind::Let; }
    };

    struct simple_expr_call : simple_expr {
        name m_name;
        std::vector<name> m_args;
        int m_direct;
        simple_expr_call(name m_name, std::vector<name> m_args)
            : m_name(m_name), m_args(m_args), m_direct(0) {
            this->m_kind = simple_expr_kind::Call;
        }
        simple_expr_call(name m_name, std::vector<name> m_args, int direct)
            : m_name(m_name), m_args(m_args), m_direct(direct) {
            this->m_kind = simple_expr_kind::Call;
        }
        virtual simple_expr_kind kind() const { return simple_expr_kind::Call; }
    };

    struct simple_expr_closure_alloc : simple_expr {
        name m_name;
        std::vector<name> m_free_vars;
        int m_arity;

        simple_expr_closure_alloc(name m_name, std::vector<name> m_free_vars, int m_arity)
            : m_name(m_name), m_free_vars(m_free_vars), m_arity(m_arity) {
            this->m_kind = simple_expr_kind::ClosureAlloc;
        }

        virtual simple_expr_kind kind() const { return simple_expr_kind::ClosureAlloc; }
    };


    struct simple_expr_switch : simple_expr {
        name m_scrutinee;
        std::vector<shared_ptr<simple_expr>> m_cases;
        simple_expr_switch(name m_scrutinee, std::vector<shared_ptr<simple_expr>> m_cases)
            : m_scrutinee(m_scrutinee), m_cases(m_cases) {
                this->m_kind = simple_expr_kind::Switch;
        }
        virtual simple_expr_kind kind() const { return simple_expr_kind::Switch; }
    };

    struct simple_expr_project : simple_expr {
        name m_name;
        int m_index;
        simple_expr_project(name m_name, int m_index)
            : m_name(m_name), m_index(m_index) {
                this->m_kind = simple_expr_kind::Project;
        }
        virtual simple_expr_kind kind() const { return simple_expr_kind::Project; }
    };

    struct simple_expr_error : simple_expr {
        std::string m_error_msg;
        simple_expr_error(std::string msg) : m_error_msg(msg) {}
        virtual simple_expr_kind kind() const { return simple_expr_kind::Error; }
    };

    inline bool simple_is_let(simple_expr const & e) {
        return e.kind() == simple_expr_kind::Let;
    }

    inline bool simple_is_call(simple_expr const & e) {
        return e.kind() == simple_expr_kind::Call;
    }

    inline bool simple_is_error(simple_expr const & e) {
        return e.kind() == simple_expr_kind::Error;
    }

    inline bool simple_is_var(simple_expr const & e) {
        return e.kind() == simple_expr_kind::SVar;
    }

    inline bool simple_is_switch(simple_expr const & e) {
        return e.kind() == simple_expr_kind::Switch;
    }

    inline bool simple_is_project(simple_expr const & e) {
        return e.kind() == simple_expr_kind::Project;
    }

    inline bool simple_is_closure_alloc(simple_expr const & e) {
        return e.kind() == simple_expr_kind::ClosureAlloc;
    }

    inline simple_expr_call const * to_simple_call(simple_expr const * e) {
        lean_assert(simple_is_call(*e));
        return static_cast<simple_expr_call const *>(e);
    }

    inline simple_expr_let const * to_simple_let(simple_expr const * e) {
        lean_assert(simple_is_let(*e));
        return static_cast<simple_expr_let const *>(e);
    }

    inline simple_expr_error const * to_simple_error(simple_expr const * e) {
        lean_assert(simple_is_error(*e));
        return static_cast<simple_expr_error const *>(e);
    }

    inline simple_expr_var const * to_simple_var(simple_expr const * e) {
        lean_assert(simple_is_var(*e));
        return static_cast<simple_expr_var const *>(e);
    }

    inline simple_expr_switch const * to_simple_switch(simple_expr const * e) {
        lean_assert(simple_is_switch(*e));
        return static_cast<simple_expr_switch const *>(e);
    }

    inline simple_expr_project const * to_simple_project(simple_expr const * e) {
        lean_assert(simple_is_project(*e));
        return static_cast<simple_expr_project const *>(e);
    }

    inline simple_expr_closure_alloc const * to_simple_closure_alloc(simple_expr const * e) {
        lean_assert(simple_is_closure_alloc(*e));
        return static_cast<simple_expr_closure_alloc const *>(e);
    }
}
