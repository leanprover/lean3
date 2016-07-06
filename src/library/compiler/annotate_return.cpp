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
#include "library/vm/vm.h"

namespace lean {
class annotate_return_fn : public compiler_step_visitor {
    virtual expr visit_var(expr const & e) {
       return annotate_return(e);
    }

    virtual expr visit_local(expr const & e) {
       return annotate_return(e);
    }

    virtual expr visit_constant(expr const & e) {
        return annotate_return(e);
    }

    virtual expr visit_macro(expr const & e) {
        return annotate_return(e);
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

        if (is_internal_cases(fn) || is_constant(fn, get_nat_cases_on_name())) {
            buffer<expr> annotated_args;

            annotated_args.push_back(args[0]);

            for (unsigned i = 1; i < args.size(); i++) {
                annotated_args.push_back(visit(args[i]));
            }

            return mk_app(fn, annotated_args);
            // buffer<expr> annotated_args;
            // lean_assert(args.size() > 1);
            //
            // // We leave the scrutinee alone, control flow can not return from here.
            // annotated_args.push_back(args[0]);
            //
            // // We loop over each case, traversing the binders pushing the return
            // // to the final expression in each case.
            // for (unsigned i = 1; i < args.size(); i++) {
            //     auto case_i = args[i];
            //     buffer<expr> locals;
            //
            //     while (is_lambda(case_i)) {
            //         name n = mk_fresh_name();
            //         locals.push_back(mk_local(n, binding_domain(case_i), binding_info(case_i)));
            //         case_i = binding_body(case_i);
            //     }
            //
            //     // We then reconstruct the case and add it to the above buffer.
            //     auto annotated_body = visit(case_i);
            //     auto result = Fun(locals, annotated_body);
            //     annotated_args.push_back(result);
            // }
            // return mk_app(fn, annotated_args);
        } else {
            return annotate_return(e);
        }
    }
    //
    expr annotate_return(expr const & e) {
        return mk_app(mk_constant(name({"native_compiler", "return"})), e);
    }

public:
    annotate_return_fn(environment const & env):compiler_step_visitor(env) {}
};

expr annotate_return(environment const & env, expr const & e) {
    return annotate_return_fn(env)(e);
}
}
