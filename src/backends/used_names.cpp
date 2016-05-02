/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/

#include <iostream>
#include <utility>
#include "used_names.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "kernel/type_checker.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {
used_defs::used_defs(environment const & env) : m_env(env) {
    this->m_used_names = name_set();
    this->m_names_to_process = std::vector<name>();
}

// Add a name to the live name set, marking
// marking it as seen, and queuing it to be processed.
void used_defs::add_name(name const & n) {
    if (!this->m_used_names.contains(n)) {
        this->m_used_names.insert(n);
        this->m_names_to_process.push_back(n);
    }
}

void used_defs::names_in_decl(declaration const & d) {
    auto n = d.get_name();

    // Start with the name of the current decl,
    // we then will collect, the set of names in
    // the body, and push them on to the stack to
    // be processed, we will repeat this until,
    // the stack is empty.
    this->add_name(n);

    if (d.is_definition()) {
        // Get the names from the body.
        auto body = d.get_value();
        this->names_in_expr(body);
    }

    // Finally we need to recursively process the
    // remaining definitions to full compute the
    // working set.
    while (!this->m_names_to_process.empty()) {
        auto n = this->m_names_to_process.back();
        this->m_names_to_process.pop_back();
        this->names_in_decl(this->m_env.get(n));
    }

    lean_assert(this->m_names_to_process.empty());
}

void used_defs::names_in_expr(expr const & e) {
    std::cout << "exp: " << e << std::endl;
    switch (e.kind()) {
        case expr_kind::Local: case expr_kind::Meta:
            break;
        case expr_kind::Var:
            std::cout << "var: " << e << std::endl;
            break;
        case expr_kind::Sort:
            break;
        case expr_kind::Constant:
            this->add_name(const_name(e));
            break;
        case expr_kind::Macro: {
            type_checker tc(m_env);
            auto expanded_macro = tc.expand_macro(e);
            lean_assert(expanded_macro);
            names_in_expr(expanded_macro.value());
            break;
        }
        case expr_kind::Lambda:
        case expr_kind::Pi: {
            buffer<expr> ls;
            auto ex = e;
            while (is_binding(ex)) {
                expr d = instantiate_rev(binding_domain(ex), ls.size(), ls.data());
                this->names_in_expr(d);
                auto n = mk_fresh_name(); // (name const & prefix, unsigned k);
                expr l = mk_local(n, binding_name(ex), d, binding_info(ex));
                ls.push_back(l);
                ex = binding_body(ex);
            }
            ex = instantiate_rev(ex, ls.size(), ls.data());
            this->names_in_expr(ex);
            break;
        }
        case expr_kind::App:
            this->names_in_expr(app_fn(e));
            this->names_in_expr(app_arg(e));
        case expr_kind::Let:
            break;
    }
}
}
