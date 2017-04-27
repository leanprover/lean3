/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/

#include "library/attribute_manager.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm_declaration.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/pos_info_provider.h"
#include "library/vm/vm_pos_info_provider.h"

#ifndef LEAN_DEFAULT_LINTER
#define LEAN_DEFAULT_LINTER true
#endif

namespace lean {

static lean::name * g_linter = nullptr;

buffer<name> get_linters(environment const & env) {
    buffer<name> ns;
    get_attribute(env, *g_linter).get_instances(env, ns);
    return ns;
}

void lint_declaration(environment const &env, pos_info_provider const &prov,
                      declaration const &decl) {
    auto opts = get_global_ios().get_options();
    vm_state S(env, opts);
    scope_vm_state scoped(S);

    local_context lctx;
    tactic_state tac_st = mk_tactic_state_for(env, opts, {"Linter"}, lctx, mk_constant("true"));

    auto linter_names = get_linters(env);
    for (auto linter_name : linter_names) {
        // NB: because we currently have 1 field inductive, this requires no unboxing
        auto linter_fn = S.get_constant(linter_name);
        vm_obj linter_result = S.invoke(linter_fn, to_obj(prov), to_obj(decl), to_obj(tac_st));
        if (is_constructor(linter_result) && cidx(linter_result) == 0) {
            return; // to_format(cfield(linter_result ,0));
        } else if (auto except = tactic::is_exception(S, linter_result)) {
            auto msg = std::get<0>(*except);
            throw lean::exception((sstream() << msg).str());
        } else {
            lean_unreachable();
        }
    }
}

bool linting_enabled(options const & opts) {
    return opts.get_bool(*g_linter, LEAN_DEFAULT_LINTER);
}

void initialize_linter() {
    g_linter = new name{"linter"};

    register_system_attribute(basic_attribute::with_check(
            "linter", "a declaration linter",
            [](environment const & env, name const & decl_name, bool) {
                auto decl = env.find(decl_name);
                std::cout << "in linter check" << decl->get_type() << std::endl;
                // throw exception("invalid '[parsing_only]' attribute, can only be used in notation declarations");
            }));

    register_bool_option(*g_linter, LEAN_DEFAULT_LINTER, "(linter) enable the linting framework");
}

void finalize_linter() {
    delete g_linter;
}
}
