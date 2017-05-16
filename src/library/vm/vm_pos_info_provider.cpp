/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include "library/vm/vm_pos_info.h"
#include "kernel/pos_info_provider.h"
#include "kernel/scope_pos_info_provider.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_option.h"
#include "library/tactic/tactic_state.h"

namespace lean {

vm_obj vm_expr_pos(vm_obj const & expr_obj, vm_obj const & st) {
    auto pos = get_pos_info_provider()->get_pos_info_or_some(to_expr(expr_obj));
    return tactic::mk_success(to_obj(pos), tactic::to_state(st));
}

void initialize_vm_pos_info_provider() {
    DECLARE_VM_BUILTIN(name({"tactic", "expr_pos"}), vm_expr_pos);
}

void finalize_vm_pos_info_provider() {}
}

