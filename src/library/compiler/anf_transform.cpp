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

bool is_cases_on(environment const & env, expr const & e) {
    return (is_constant(e) &&
    (get_vm_builtin_cases_idx(env, const_name(e)) ||
     is_internal_cases(e) ||
     is_constant(e, get_nat_cases_on_name())));
}

class anf_transform_fn : public compiler_step_visitor {
    buffer<buffer<pair<name, expr>>> m_bindings_stack;

    virtual expr visit_let(expr const & e) {
        auto ln = let_name(e);
        auto lv = visit(let_value(e));

        buffer<pair<name, expr>> & top = m_bindings_stack.back();

        top.push_back(pair<name, expr>(ln, lv));

        auto lb = visit(instantiate(let_body(e), mk_local(ln, mk_neutral_expr())));

        std::cout << "let_name: " << ln << std::endl;
        std::cout << "let_value: " << lv << std::endl;
        std::cout << "let_body: " << lb << std::endl;

        return lb;
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        buffer<expr> lifted_args;
        expr fn = get_app_args(e, args);

        if (is_cases_on(m_ctx->env(), fn)) {
            lifted_args.push_back(visit(args[0]));

            for (unsigned i = 1; i < args.size(); i++) {
                auto arg = args[i];
                buffer<expr> locals;
                this->m_bindings_stack.push_back(buffer<pair<name, expr>>());
                auto ret_e = collect_bindings(arg, locals);
                ret_e = mk_scoped_let(ret_e);
                this->m_bindings_stack.pop_back();
                lifted_args.push_back(Fun(locals, ret_e));
            }

            return mk_app(fn, lifted_args);
        } else {
            buffer<pair<name, expr>> & scope = this->m_bindings_stack.back();

            for (auto arg : args) {
                auto n = mk_fresh_name();
                auto local = mk_local(n, mk_neutral_expr());
                scope.push_back(pair<name, expr>(n, arg));
                lifted_args.push_back(local);
            }

            if (!is_constant(fn)) {
                auto n = mk_fresh_name();
                auto fn_local = mk_local(n, mk_neutral_expr());
                scope.push_back(pair<name, expr>(n, fn));
                return mk_app(fn_local, lifted_args);
            } else {
                return mk_app(fn, lifted_args);
            }
        }
    }

    // virtual expr visit_let(expr const & e) {
    //     auto lb = let_body(e);
    //
    //     while (is_let(lv)) {
    //         expr v = instantiate_rev(let_value(lv), lifted_lets.size(), lifted_lets.data());
    //         lifted_lets.push_let(let_name(lv), mk_neutral_expr(), v);
    //         lv = v;
    //     }
    //
    //     lifted_lets.push_let(ln, mk_neutral_expr(), lv);
    //
    //     return lifted_lets.mk_let(lb);
    // }

    expr collect_bindings(expr const & e_, buffer<expr> & locals) {
        expr e = e_;
        while (is_lambda(e)) {
            name n = mk_fresh_name();
            locals.push_back(mk_local(n, mk_neutral_expr()));
            e = binding_body(e);
        }
        e = instantiate_rev(e, locals.size(), locals.data());
        return visit(e);
    }

    expr mk_scoped_let(expr const & e) {
        auto scope = m_bindings_stack.back();
        unsigned i = scope.size();

        for (auto binding : scope) {
            std::cout << binding.first << binding.second << std::endl;
        }

        expr ret_e = e;

        while (i != 0) {
          auto binding = scope[i - 1];
          auto body = abstract(ret_e, mk_local(binding.first, mk_neutral_expr()));
          ret_e = mk_let(binding.first, mk_neutral_expr(), binding.second, body);
          i--;
        }

        return ret_e;
    }
public:
    expr operator()(expr const & e) {
        std::cout << "expression here" << e << std::endl;
        buffer<expr> locals;
        auto ret_e = collect_bindings(e, locals);

        std::cout << "visited expr" << ret_e << std::endl;
        lean_assert(m_bindings_stack.size() == 1);
        ret_e = this->mk_scoped_let(ret_e);
        std::cout << "final expr" << ret_e << std::endl;
        return Fun(locals, ret_e);
    }

    anf_transform_fn(environment const & env):
    compiler_step_visitor(env), m_bindings_stack(buffer<buffer<pair<name, expr>>>()) {
      m_bindings_stack.push_back(buffer<pair<name, expr>>());
    }
};

expr anf_transform(environment const & env, expr const & e) {
    return anf_transform_fn(env)(e);
}
}
