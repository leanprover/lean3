/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/sorry.h"
#include "library/util.h"
#include "library/normalize.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/simplify.h"
#include "library/compiler/util.h"
#include "library/compiler/inliner.h"

namespace lean {
static name * g_comp_simp = nullptr;
static simp_lemmas_token g_comp_simp_tk;

static simp_config get_comp_simp_config() {
    simp_config cfg;
    cfg.m_max_steps          = 1000000;
    cfg.m_contextual         = false;
    cfg.m_lift_eq            = false;
    /* Remark: m_canonize_instances is not efficient when target contains expressions of the form:
       ```
       if cmd = "step" ∨ cmd = "s" then ...
       ```

       TODO(Leo): investigate where the problem is. It is probably related to the (decidable_eq string)
       instance.
    */
    cfg.m_canonize_instances = false;
    cfg.m_canonize_proofs    = false;
    cfg.m_use_axioms         = true;
    cfg.m_proj               = true;
    /*
       TODO(Leo): we need a custom simplifier for the compiler.
       - No proofs.
       - Let-decl elimination.
       - ((fun x, t) s) ==> (let x := t in s) instead of t[x/s]
    */
    cfg.m_beta               = true;
    cfg.m_iota               = false;
    cfg.m_iota_eqn           = false;
    cfg.m_eta                = false;
    cfg.m_zeta               = false;
    cfg.m_constructor_eq     = false;
    return cfg;
}

class comp_simp_fn : public simplify_fn {
    /* Erase proof terms and ignore types */
    virtual optional<pair<simp_result, bool>> pre(expr const & e, optional<expr> const &) override {
        if (is_sorry(e))
            return optional<pair<simp_result, bool>>();
        expr type = m_ctx.infer(e);
        expr norm_type = m_ctx.whnf(type);
        if (is_sort(norm_type)) {
            /* e is a type, so we instruct simplifier to ignore it */
            return optional<pair<simp_result, bool>>(simp_result(e), false /* do not visit result */);
        } else if (m_ctx.is_prop(norm_type)) {
            /* e is a proof, we replace it with a sorry */
            expr r = mk_sorry(type, true);
            return optional<pair<simp_result, bool>>(simp_result(r), false /* do not visit result */);
        } else {
            return optional<pair<simp_result, bool>>();
        }
    }

    /* ===========================
       Begin of section copied from inliner.cpp
       =========================== */

    /* Try to reduce cases_on (and nonrecursive recursor) application
       if major became a constructor */
    expr visit_cases_on_app(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_constant(fn));
        bool is_cases_on            = is_cases_on_recursor(env(), const_name(fn));
        name const & rec_name       = const_name(fn);
        name const & I_name         = rec_name.get_prefix();
        unsigned nparams            = *inductive::get_num_params(env(), I_name);
        unsigned nindices           = *inductive::get_num_indices(env(), I_name);
        unsigned major_idx;
        if (is_cases_on) {
            major_idx       = nparams + 1 + nindices;
        } else {
            major_idx       = *inductive::get_elim_major_idx(env(), rec_name);
        }
        if (major_idx >= args.size())
            return copy_tag(e, mk_app(fn, args));
        expr major = beta_reduce(args[major_idx]);
        if (is_constructor_app(env(), major)) {
            /* Major premise became a constructor. So, we should reduce. */
            expr new_e = copy_tag(e, mk_app(fn, args));
            if (is_cases_on) {
                /* unfold cases_on */
                if (auto r = unfold_term(env(), new_e))
                    new_e = *r;
                else
                    return new_e;
            }
            /* reduce */
            if (auto r = m_ctx.norm_ext(new_e))
                return copy_tag(e, beta_reduce(*r));
        }
        return copy_tag(e, mk_app(fn, args));
    }

    bool is_nonrecursive_recursor(name const & n) {
        if (auto I_name = inductive::is_elim_rule(env(), n)) {
            return !is_recursive_datatype(env(), *I_name);
        }
        return false;
    }

    /* ===========================
       End of section copied from inliner.cpp
       =========================== */

    optional<expr> try_to_inline(expr const & e) {
        if (!is_app(e))
            return none_expr();
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return none_expr();
        name const & n  = const_name(fn);
        if (is_vm_builtin_function(n) || is_pack_unpack(env(), e))
            return none_expr();
        if (is_cases_on_recursor(env(), n) || is_nonrecursive_recursor(n))
            return some_expr(visit_cases_on_app(e));
        /* We only inline declarations marked with @[inline]. We don't use any heuristic. */
        if (is_inline(env(), n)) {
            /* check if we have n._comp_simp summary in the environment */
            name new_n(n, "_comp_simp");
            expr new_e;
            if (env().find(new_n)) {
                buffer<expr> args;
                get_app_args(e, args);
                new_e = mk_app(mk_constant(new_n, const_levels(fn)), args);
            } else {
                new_e = e;
            }
            if (auto r = unfold_term(env(), new_e)) {
                return some_expr(copy_tag(e, expr(*r)));
            }
        }
        return none_expr();
    }

    virtual optional<pair<simp_result, bool>> post(expr const & e, optional<expr> const & parent) override {
        expr new_e = e;
        /* Apply rewrite rules first */
        bool progress = false;
        if (auto r = simplify_fn::post(new_e, parent)) {
            new_e = r->first.get_new();
            progress = true;
        }

        if (auto r = try_to_inline(e)) {
            new_e = *r;
            progress = true;
        }

        if (progress) {
            return optional<pair<simp_result, bool>>(simp_result(new_e), true);
        } else {
            return optional<pair<simp_result, bool>>();
        }
    }


public:
    comp_simp_fn(type_context_old & ctx, defeq_canonizer::state & dcs, simp_lemmas const & slss, simp_config const & cfg):
        simplify_fn(ctx, dcs, slss, list<name>(), cfg) {}
};

pair<environment, expr> apply_comp_simp(environment const & env, name const & decl_name, expr const & e) {
    type_context_old ctx(env);
    simp_config cfg = get_comp_simp_config();
    defeq_canonizer::state dcs;
    simp_lemmas lemmas = get_simp_lemmas(env, g_comp_simp_tk);
    comp_simp_fn simplifier(ctx, dcs, lemmas, cfg);
    try {
        simp_result r = simplifier(get_eq_name(), e);
        expr new_e    = r.get_new();
        if (new_e != e) {
            declaration decl = env.get(decl_name);
            declaration new_decl = mk_definition(name(decl_name, "_comp_simp"),
                                                 decl.get_univ_params(),
                                                 decl.get_type(),
                                                 new_e,
                                                 decl.get_hints(),
                                                 false);
            certified_declaration cdecl = check(env, new_decl, true /* check immediately */);
            environment new_env = env.add(cdecl);
            return mk_pair(new_env, new_e);
        } else {
            return mk_pair(env, e);
        }
    } catch (exception &) {
        return mk_pair(env, e);
    }
}

void initialize_comp_simp() {
    g_comp_simp    = new name("comp_simp");
    g_comp_simp_tk = register_simp_attribute(*g_comp_simp, {*g_comp_simp}, {});
}

void finalize_comp_simp() {
    delete g_comp_simp;
}
}
