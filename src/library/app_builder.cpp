/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/scoped_map.h"
#include "util/name_map.h"
#include "kernel/instantiate.h"
#include "library/match.h"
#include "library/app_builder.h"
#include "library/kernel_bindings.h"
#include "library/tmp_type_context.h"

namespace lean {
struct app_builder::imp {
    std::unique_ptr<tmp_type_context> m_ctx;

    struct entry {
        unsigned             m_num_umeta;
        unsigned             m_num_emeta;
        expr                 m_app;
        list<optional<expr>> m_inst_args; // "mask" of implicit instance arguments
        list<expr>           m_expl_args; // metavars for explicit arguments

        /*
          IMPORTANT: for m_inst_args we store the arguments in reverse order.
          For example, the first element in the list indicates whether the last argument
          is an instance implicit argument or not. If it is not none, then the element
          is the associated metavariable

          m_expl_args are also stored in reverse order
        */
    };

    struct key {
        name       m_name;
        unsigned   m_num_expl;
        unsigned   m_hash;
        // If nil, then the mask is composed of the last m_num_expl arguments.
        // If nonnil, then the mask is NOT of the form [false*, true*]
        list<bool> m_mask;

        static bool is_simple(list<bool> const & mask) {
            bool found_true = false;
            for (bool b : mask) {
                if (b) {
                    found_true = true;
                } else if (found_true) {
                    // found (true, false)
                    return false;
                }
            }
            return true;
        }

        key(name const & c, unsigned n):
            m_name(c), m_num_expl(n),
            m_hash(::lean::hash(c.hash(), n)) {
        }

        key(name const & c, list<bool> const & m):
            m_name(c), m_num_expl(length(m)) {
            m_hash = ::lean::hash(c.hash(), m_num_expl);
            if (!is_simple(m)) {
                m_mask = m;
                for (bool b : m) {
                    if (b)
                        m_hash = ::lean::hash(m_hash, 17u);
                    else
                        m_hash = ::lean::hash(m_hash, 31u);
                }
            }
        }

        bool check_invariant() const {
            lean_assert(empty(m_mask) || length(m_mask) == m_num_expl);
            lean_assert(empty(m_mask) || !is_simple(m_mask));
            return true;
        }

        unsigned hash() const {
            return m_hash;
        }

        friend bool operator==(key const & k1, key const & k2) {
            return k1.m_name == k2.m_name && k1.m_num_expl == k2.m_num_expl && k1.m_mask == k2.m_mask;
        }
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.hash(); }
    };

    typedef std::unordered_map<key, entry, key_hash_fn> map;

    map m_map;

    imp(environment const & env, io_state const & ios, reducible_behavior b):
        m_ctx(new tmp_type_context(env, ios, b)) {
    }

    imp(std::unique_ptr<tmp_type_context> && ctx):
        m_ctx(std::move(ctx)) {
    }

    levels mk_metavars(declaration const & d, buffer<expr> & mvars, buffer<optional<expr>> & inst_args) {
        m_ctx->clear();
        unsigned num_univ = d.get_num_univ_params();
        buffer<level> lvls_buffer;
        for (unsigned i = 0; i < num_univ; i++) {
            lvls_buffer.push_back(m_ctx->mk_uvar());
        }
        levels lvls = to_list(lvls_buffer);
        expr type   = m_ctx->whnf(instantiate_type_univ_params(d, lvls));
        while (is_pi(type)) {
            expr mvar = m_ctx->mk_mvar(binding_domain(type));
            if (binding_info(type).is_inst_implicit())
                inst_args.push_back(some_expr(mvar));
            else
                inst_args.push_back(none_expr());
            mvars.push_back(mvar);
            type = m_ctx->whnf(instantiate(binding_body(type), mvar));
        }
        return lvls;
    }

    optional<entry> get_entry(name const & c, unsigned nargs) {
        key k(c, nargs);
        lean_assert(k.check_invariant());
        auto it = m_map.find(k);
        if (it == m_map.end()) {
            if (auto d = m_ctx->env().find(c)) {
                buffer<expr> mvars;
                buffer<optional<expr>> inst_args;
                levels lvls = mk_metavars(*d, mvars, inst_args);
                if (nargs > mvars.size())
                    return optional<entry>(); // insufficient number of arguments
                entry e;
                e.m_num_umeta = d->get_num_univ_params();
                e.m_num_emeta = mvars.size();
                e.m_app       = ::lean::mk_app(mk_constant(c, lvls), mvars);
                e.m_inst_args = reverse_to_list(inst_args.begin(), inst_args.end());
                e.m_expl_args = reverse_to_list(mvars.begin() + mvars.size() - nargs, mvars.end());
                m_map.insert(mk_pair(k, e));
                return optional<entry>(e);
            } else {
                return optional<entry>(); // unknown decl
            }
        } else {
            return optional<entry>(it->second);
        }
    }

    bool check_all_assigned(entry const & e) {
        lean_assert(e.m_num_emeta == length(e.m_inst_args));
        // recall that the flags at e.m_inst_args are stored in reverse order.
        // For example, the first flag in the list indicates whether the last argument
        // is an instance implicit argument or not.
        unsigned i = e.m_num_emeta;
        for (optional<expr> const & inst_arg : e.m_inst_args) {
            lean_assert(i > 0);
            --i;
            if (inst_arg) {
                expr type = m_ctx->instantiate_uvars_mvars(mlocal_type(*inst_arg));
                if (auto v = m_ctx->mk_class_instance(type)) {
                    if (!m_ctx->force_assign(*inst_arg, *v))
                        return false;
                } else {
                    return false;
                }
            }
            if (!m_ctx->is_mvar_assigned(i))
                return false;
        }
        for (unsigned i = 0; i < e.m_num_umeta; i++) {
            if (!m_ctx->is_uvar_assigned(i))
                return false;
        }
        return true;
    }

    optional<expr> mk_app(name const & c, unsigned nargs, expr const * args) {
        optional<entry> e = get_entry(c, nargs);
        if (!e)
            return none_expr();
        m_ctx->clear();
        m_ctx->set_next_uvar_idx(e->m_num_umeta);
        m_ctx->set_next_mvar_idx(e->m_num_emeta);
        unsigned i = nargs;
        for (auto m : e->m_expl_args) {
            if (i == 0)
                return none_expr();
            --i;
            if (!m_ctx->assign(m, args[i]))
                return none_expr();
        }
        if (!check_all_assigned(*e))
            return none_expr();
        return some_expr(m_ctx->instantiate_uvars_mvars(e->m_app));
    }

    optional<expr> mk_app(name const & /* c */, unsigned /* mask_sz */, bool const * /* mask */, expr const * /* args */) {
        return none_expr();
    }
};

app_builder::app_builder(environment const & env, io_state const & ios, reducible_behavior b):
    m_ptr(new imp(env, ios, b)) {
}

app_builder::app_builder(environment const & env, reducible_behavior b):
    app_builder(env, get_dummy_ios(), b) {
}

app_builder::app_builder(std::unique_ptr<tmp_type_context> && ctx):
    m_ptr(new imp(std::move(ctx))) {
}

app_builder::~app_builder() {}

optional<expr> app_builder::mk_app(name const & c, unsigned nargs, expr const * args) {
    return m_ptr->mk_app(c, nargs, args);
}

optional<expr> app_builder::mk_app(name const & c, unsigned mask_sz, bool const * mask, expr const * args) {
    return m_ptr->mk_app(c, mask_sz, mask, args);
}
}
