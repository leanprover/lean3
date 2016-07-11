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
#include "util/sstream.h"
#include "util/fresh_name.h"

namespace lean {
class anf_transform_fn : public compiler_step_visitor {
    unsigned m_counter;

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        type_context::tmp_locals m_locals(m_ctx);
        expr fn = get_app_args(e, args);

        if (
            is_internal_cases(fn) ||
            is_constant(fn, get_nat_cases_on_name())) {
            buffer<expr> anf_args;

            expr scrut = visit(args[0]);
            auto scrut_n = mk_fresh_name();
            auto scrut_local = m_locals.push_let(scrut_n, mk_neutral_expr(), scrut);
            anf_args.push_back(scrut_local);

            for (unsigned i = 1; i < args.size(); i++) {
                anf_args.push_back(visit(args[i]));
            }

            return m_locals.mk_let(mk_app(fn, anf_args));
        } else {
            buffer<expr> arg_locals;

            for (auto arg : args) {
                auto n = mk_fresh_name();
                expr v = visit(instantiate_rev(arg, m_locals.size(), m_locals.data()));
                auto local = m_locals.push_let(n, mk_neutral_expr(), v);
                arg_locals.push_back(local);
            }

            if (!is_constant(fn)) {
                auto n = mk_fresh_name();
                auto fn_local = m_locals.push_let(n, mk_neutral_expr(), fn);
                return m_locals.mk_let(mk_app(fn_local, arg_locals));
            } else {
                return m_locals.mk_let(mk_app(fn, arg_locals));
            }
        }
    }
public:
    expr operator()(expr const & e) {
        return e;
    }

    anf_transform_fn(environment const & env):
    compiler_step_visitor(env), m_counter(0) {}
};

expr anf_transform(environment const & env, expr const & e) {
    return anf_transform_fn(env)(e);
}
}
