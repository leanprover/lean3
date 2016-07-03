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
class anf_transform_fn : public compiler_step_visitor {
    buffer<pair<name, expr>> bindings;

    // virtual expr visit_var(expr const & e) {
    //    return anf_transform(e);
    // }
    //
    // virtual expr visit_local(expr const & e) {
    //    return anf_transform(e);
    // }
    //
    // virtual expr visit_constant(expr const & e) {
    //     return anf_transform(e);
    // }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);

        buffer<expr> arg_names;
        for (auto arg : args) {
            arg_names.push_back(visit(arg));
        }

        if (!is_constant(fn)) {
            return mk_app(fn, arg_names);
        } else {
            return mk_app(fn, arg_names);
        }
    }

    expr bind_exprs(expr e) {
        auto e_final = e;
        // for (auto binding : bindings) {
        //     e_final = mk_let(
        //         binding.first,
        //         mk_neutral_expr(),
        //         binding.second,
        //         e_final);
        // }
        return e_final;
    }
public:
    expr operator()(expr const & e) {
        auto final_expr = visit(e);
        return bind_exprs(final_expr);
    }

    anf_transform_fn(environment const & env):compiler_step_visitor(env) {}
};

expr anf_transform(environment const & env, expr const & e) {
    return anf_transform_fn(env)(e);
}
}
