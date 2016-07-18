/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/annotation.h"
#include "library/compiler/util.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/anf_transform.h"
#include "library/vm/vm.h"

namespace lean {
class cf_fn : public compiler_step_visitor {
    expr m_current_location;

    virtual expr visit_var(expr const & e) {
       return store(e);
    }

    virtual expr visit_local(expr const & e) {
       return store(e);
    }

    virtual expr visit_constant(expr const & e) {
       return store(e);
    }

    virtual expr visit_macro(expr const & e) {
       return store(e);
    }

    virtual expr visit_let(expr const & e) {
        auto n = let_name(e);
        auto v = let_value(e);
        auto b = let_body(e);

        if (is_app(v)) {
            buffer<expr> args;
            expr fn = get_app_args(v, args);

            if (is_constant(fn) && is_cases_on(m_ctx->env(), fn)) {
                // THis has a recursion problem
                m_current_location = mk_local(n, mk_neutral_expr());
                auto v_prime = visit(v);
                m_current_location = expr();
                auto b_prime = visit(b);
                return mk_let(n, mk_neutral_expr(), uninitialized(), initialize(n, v_prime, b_prime));
            } else {
                return mk_let(n, mk_neutral_expr(), v, visit(b));
            }
        } else {
            auto b = let_body(e);
            return mk_let(n, mk_neutral_expr(), v, visit(b));
        }
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);

        if (is_constant(fn) && is_cases_on(m_ctx->env(), fn)) {
            buffer<expr> annotated_args;

            annotated_args.push_back(args[0]);

            for (unsigned i = 1; i < args.size(); i++) {
                annotated_args.push_back(visit(args[i]));
            }

            return mk_app(fn, annotated_args);
        } else {
            return store(e);
        }
    }

    virtual expr visit_lambda(expr const & e_) {
        buffer<expr> locals;
        expr e = e_;
        while (is_lambda(e)) {
            name n = mk_fresh_name();
            locals.push_back(mk_local(n, mk_neutral_expr()));
            e = binding_body(e);
        }
        e = instantiate_rev(e, locals.size(), locals.data());
        return Fun(locals, visit(e));
    }

    expr store(expr const & e) {
        if (m_current_location != expr()) {
            return mk_app(mk_constant(name({"native_compiler", "store"})), m_current_location, e);
        } else {
            return e;
        }
    }

    expr uninitialized() {
        return mk_constant(name({"native_compiler", "uninitialized"}));
    }

    expr initialize(name const & n, expr const & cases_on, expr const & cont) {
        buffer<expr> args;
        // Local to store the result.
        args.push_back(mk_local(n, mk_neutral_expr()));

        // Each branch, which should store its result in Local.
        args.push_back(cases_on);

        // Continutation after running the branches.
        args.push_back(cont);

        return mk_app(mk_constant(name({"native_compiler", "initialize"})), args);
    }

public:
    cf_fn(environment const & env):compiler_step_visitor(env), m_current_location() {}
};

expr cf(environment const & env, expr const & e) {
    return cf_fn(env)(e);
}
}
