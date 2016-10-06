/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_option.h"
#include "library/compiler/native_compiler.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/nat_value.h"

namespace lean {

vm_obj native_is_internal_cnstr(vm_obj const & e) {
    auto opt_unsigned = is_internal_cnstr(to_expr(e));
    if (opt_unsigned) {
        std::cout << *opt_unsigned << std::endl;
        vm_obj u = to_obj(*opt_unsigned);
        return mk_vm_constructor(1, { u });
    } else {
        return mk_vm_constructor(0, {});
    }
}

vm_obj native_is_internal_cases(vm_obj const & e) {
    auto opt_unsigned = is_internal_cases(to_expr(e));
    if (opt_unsigned) {
        std::cout << *opt_unsigned << std::endl;
        vm_obj u = to_obj(*opt_unsigned);
        return mk_vm_constructor(1, { u });
    } else {
        return mk_vm_constructor(0, {});
    }
}

vm_obj native_is_internal_proj(vm_obj const & e) {
    auto opt_unsigned = is_internal_proj(to_expr(e));
    if (opt_unsigned) {
        std::cout << *opt_unsigned << std::endl;
        vm_obj u = to_obj(*opt_unsigned);
        return mk_vm_constructor(1, { u });
    } else {
        return mk_vm_constructor(0, {});
    }
}

vm_obj native_get_nat_value(vm_obj const & o) {
    expr e = to_expr(o);
    if (is_nat_value(e)) {
        auto n = mk_vm_nat(get_nat_value_value(e));
        return mk_vm_constructor(1, { n });
    } else {
        return mk_vm_simple(0);
    }
}

vm_obj native_get_builtin(vm_obj const & o) {
    name n = to_name(o);
    auto efn = get_builtin(n);
    if (efn) {
        std::cout << efn->m_name << std::endl;
        std::cout << efn->m_arity << std::endl;
        auto pair = mk_vm_constructor(0, { to_obj(efn->m_name), mk_vm_simple(efn->m_arity) });
        return mk_vm_some(pair);
    } else {
        return mk_vm_none();
    }
}

void initialize_vm_native() {
    // Not sure if we should expose ese or what?
    DECLARE_VM_BUILTIN(name({"native", "is_internal_cnstr"}), native_is_internal_cnstr);
    DECLARE_VM_BUILTIN(name({"native", "is_internal_cases"}), native_is_internal_cases);
    DECLARE_VM_BUILTIN(name({"native", "is_internal_proj"}), native_is_internal_proj);
    DECLARE_VM_BUILTIN(name({"native", "get_nat_value"}), native_get_nat_value);
    DECLARE_VM_BUILTIN(name({"native", "get_builtin"}), native_get_builtin);
}

void finalize_vm_native() {
}
}
