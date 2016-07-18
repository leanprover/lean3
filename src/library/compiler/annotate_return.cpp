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
// causes a linking error? not sure why?
// #include "library/compiler/cf.h"
#include "library/vm/vm.h"

namespace lean {

class annotate_return_fn : public compiler_step_visitor {
    virtual expr visit_var(expr const & e) {
       return annotate(e);
    }

    virtual expr visit_local(expr const & e) {
       return annotate(e);
    }

    virtual expr visit_constant(expr const & e) {
        return annotate(e);
    }

    virtual expr visit_macro(expr const & e) {
        return annotate(e);
    }

    virtual expr visit_let(expr const & e) {
        auto n = let_name(e);
        auto v = let_value(e);

        auto b = let_body(e);
        return mk_let(n, mk_neutral_expr(), v, visit(b));
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
        } if (mk_constant(name({"native_compiler", "initialize"})) == fn) {
            return mk_app(fn, args[0], args[1], visit(args[2]));
        } else {
            return annotate(e);
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

    expr annotate(expr const & e) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);

        if (mk_constant(name({"native_compiler", "store"})) == fn) {
            return e;
        } else {
            return mk_app(mk_constant(name({"native_compiler", "return"})), e);
        }
    }
public:
    annotate_return_fn(environment const & env):compiler_step_visitor(env) {}
};

expr annotate_return(environment const & env, expr const & e) {
    return annotate_return_fn(env)(e);
}
}
