/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/

#include "free_vars.h"
#include "kernel/expr.h"

namespace lean  {
    // De-dup this logic.
    bool is_erasible2(expr const & e) {
        //lean_trace(name({"backend", "is_erasible"}),
        //          tout() << "erase: " << e << "\n";);

        if (is_sort(e)) {
            return true;
        } else if (is_pi(e)) {
            auto co_domain = e;
            while (is_pi(co_domain)) {
                co_domain = binding_body(co_domain);
            }
            return is_sort(co_domain);
        } else {
            return false;
        }
    }

    void free_vars(expr const & e, buffer<name> & ns) {
        switch (e.kind()) {
            case expr_kind::Local:
                if (!is_erasible2(mlocal_type(e))) {
                    ns.push_back(mlocal_name(e));
                }
                break;
            case expr_kind::Macro: {
                // not sure what to do here: return this->compile_expr_macro(e, bindings);
                break;
            }
            case expr_kind::Pi:
            case expr_kind::Lambda: {
                // free_vars(binding_domain(e), ns);
                free_vars(binding_body(e), ns);
                break;
            }
            case expr_kind::App: {
                free_vars(app_fn(e), ns);
                free_vars(app_arg(e), ns);
                break;
            }
            case expr_kind::Let: {
                free_vars(let_value(e), ns);
                free_vars(let_body(e), ns);
                break;
            }
            case expr_kind::Constant:
            case expr_kind::Var:
            case expr_kind::Meta:
            case expr_kind::Sort:
                break;
        }
    }
}
