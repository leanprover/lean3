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
        Error,
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
    // inline bool is_var(expr_ptr e)         { return e->kind() == expr_kind::Var; }
    // inline bool is_constant(expr_ptr e)    { return e->kind() == expr_kind::Constant; }
    // inline bool is_local(expr_ptr e)       { return e->kind() == expr_kind::Local; }
    // inline bool is_metavar(expr_ptr e)     { return e->kind() == expr_kind::Meta; }
    // inline bool is_macro(expr_ptr e)       { return e->kind() == expr_kind::Macro; }
    // inline bool is_app(expr_ptr e)         { return e->kind() == expr_kind::App; }
    // inline bool is_lambda(expr_ptr e)      { return e->kind() == expr_kind::Lambda; }
    // inline bool is_pi(expr_ptr e)          { return e->kind() == expr_kind::Pi; }
    // inline bool is_let(expr_ptr e)         { return e->kind() == expr_kind::Let; }
    // inline bool is_sort(expr_ptr e)        { return e->kind() == expr_kind::Sort; }
    // inline bool is_binding(expr_ptr e)     { return is_lambda(e) || is_pi(e); }
    // inline bool is_mlocal(expr_ptr e)      { return is_metavar(e) || is_local(e); }
    //
    // inline expr_var *         to_var(expr_ptr e)        { lean_assert(is_var(e));         return static_cast<expr_var*>(e); }
    // inline expr_const *       to_constant(expr_ptr e)   { lean_assert(is_constant(e));    return static_cast<expr_const*>(e); }
    // inline expr_app *         to_app(expr_ptr e)        { lean_assert(is_app(e));         return static_cast<expr_app*>(e); }
    // inline expr_binding *     to_binding(expr_ptr e)    { lean_assert(is_binding(e));     return static_cast<expr_binding*>(e); }
    // inline expr_sort *        to_sort(expr_ptr e)       { lean_assert(is_sort(e));        return static_cast<expr_sort*>(e); }
    // inline expr_mlocal *      to_mlocal(expr_ptr e)     { lean_assert(is_mlocal(e));      return static_cast<expr_mlocal*>(e); }
    // inline expr_local *       to_local(expr_ptr e)      { lean_assert(is_local(e));       return static_cast<expr_local*>(e); }
    // inline expr_mlocal *      to_metavar(expr_ptr e)    { lean_assert(is_metavar(e));     return static_cast<expr_mlocal*>(e); }
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
    // inline expr_macro *       to_macro(expr_ptr e)      { lean_assert(is_macro(e));       return static_cast<expr_macro*>(e); }
}
