/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/scope_pos_info_provider.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/quote.h"
#include "library/string.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_int.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_pos_info.h"
#include "library/vm/vm_list.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/util.h"

namespace lean {
vm_obj pexpr_of_expr(vm_obj const & e) {
    return to_obj(mk_as_is(to_expr(e)));
}

vm_obj expr_to_string(vm_obj const &);

vm_obj pexpr_to_string(vm_obj const & e) {
    return expr_to_string(e);
}

vm_obj pexpr_to_raw_expr(vm_obj const & e) {
    return e;
}

vm_obj pexpr_of_raw_expr(vm_obj const & e) {
    return e;
}

vm_obj pexpr_mk_placeholder() {
    return to_obj(mk_expr_placeholder());
}

vm_obj pexpr_pos(vm_obj const & e) {
    if (auto p = get_pos_info(to_expr(e)))
        return mk_vm_some(to_obj(*p));
    return mk_vm_none();
}

vm_obj pexpr_mk_explicit(vm_obj const & e) {
    return to_obj(mk_explicit(to_expr(e)));
}

vm_obj pexpr_mk_field_macro(vm_obj const & e, vm_obj const & fname) {
    return to_obj(mk_field_notation(to_expr(e), to_name(fname)));
}

unsigned pexpr_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    expr const & e = to_expr(o);
    // std::cout << "into pexpr cases on: " << e << std::endl;
    switch (e.kind()) {
    case expr_kind::Var:
        data.push_back(mk_vm_nat(var_idx(e)));
        break;
    case expr_kind::Sort:
        data.push_back(to_obj(sort_level(e)));
        break;
    case expr_kind::Constant:
        data.push_back(to_obj(const_name(e)));
        data.push_back(to_obj(const_levels(e)));
        break;
    case expr_kind::Meta:
        data.push_back(to_obj(mlocal_name(e)));
        data.push_back(to_obj(mlocal_type(e)));
        break;
    case expr_kind::Local:
        data.push_back(to_obj(mlocal_name(e)));
        data.push_back(to_obj(local_pp_name(e)));
        data.push_back(to_obj(local_info(e)));
        data.push_back(to_obj(mlocal_type(e)));
        break;
    case expr_kind::App:
        data.push_back(to_obj(app_fn(e)));
        data.push_back(to_obj(app_arg(e)));
        break;
    case expr_kind::Lambda:
    case expr_kind::Pi:
        data.push_back(to_obj(binding_name(e)));
        data.push_back(to_obj(binding_info(e)));
        data.push_back(to_obj(binding_domain(e)));
        data.push_back(to_obj(binding_body(e)));
        break;
    case expr_kind::Let:
        data.push_back(to_obj(let_name(e)));
        data.push_back(to_obj(let_type(e)));
        data.push_back(to_obj(let_value(e)));
        data.push_back(to_obj(let_body(e)));
        break;
    case expr_kind::Macro:
        auto macro_name = macro_def(e).get_name();
        // We place all the special macro constructors at the
        // end of the inductive declaration so they should
        // be the ctor index for macro +1, +2, etc.
        if (macro_name == "prenum") {
            data.push_back(mk_vm_nat(prenum_value(e)));
            return static_cast<unsigned>(e.kind()) + 1;
        } else if (equations == "equations") {
            // data.push_back(to_obj(macro_def(e)));
            // data.push_back(mk_vm_nat(macro_num_args(e)));
            // data.push_back(mk_vm_closure(g_expr_macro_arg_fun_idx, 1, &o));
            std::cout << macro_def(e).get_name() << std::endl;
            throw "foooo";
        }
        break;
    }
    return static_cast<unsigned>(e.kind());
}

void initialize_vm_pexpr() {
    DECLARE_VM_BUILTIN(name({"pexpr", "subst"}),          expr_subst);
    DECLARE_VM_BUILTIN(name({"pexpr", "of_expr"}),        pexpr_of_expr);
    DECLARE_VM_BUILTIN(name({"pexpr", "to_string"}),      pexpr_to_string);
    DECLARE_VM_BUILTIN(name({"pexpr", "of_raw_expr"}),    pexpr_of_raw_expr);
    DECLARE_VM_BUILTIN(name({"pexpr", "to_raw_expr"}),    pexpr_to_raw_expr);
    DECLARE_VM_BUILTIN(name({"pexpr", "mk_placeholder"}), pexpr_mk_placeholder);

    DECLARE_VM_BUILTIN(name("pexpr", "pos"),              pexpr_pos);

    DECLARE_VM_BUILTIN(name("pexpr", "mk_explicit"),      pexpr_mk_explicit);
    DECLARE_VM_BUILTIN(name("pexpr", "mk_field_macro"),   pexpr_mk_field_macro);

    DECLARE_VM_CASES_BUILTIN(name({"pexpr", "cases_on"}),   pexpr_cases_on);
}

void finalize_vm_pexpr() {
}
}
