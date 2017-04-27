/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include "library/vm/vm_pos_info.h"
#include "kernel/pos_info_provider.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_option.h"

namespace lean {

struct vm_pos_info_provider : public vm_external {
    pos_info_provider const & m_val;

    vm_pos_info_provider(pos_info_provider const & v) : m_val(v) {}
    virtual ~vm_pos_info_provider() {}

    virtual void dealloc() override {
        this->~vm_pos_info_provider();
        get_vm_allocator().deallocate(sizeof(vm_pos_info_provider), this);
    }

    virtual vm_external * ts_clone(vm_clone_fn const &) override {
        return new vm_pos_info_provider(m_val);
    }
    virtual vm_external * clone(vm_clone_fn const &) override {
        lean_unreachable();
    }
};

pos_info_provider const & to_pos_info_provider(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_pos_info_provider *>(to_external(o)));
    return static_cast<vm_pos_info_provider*>(to_external(o))->m_val;
}

vm_obj to_obj(pos_info_provider const & p) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_pos_info_provider))) vm_pos_info_provider(p));
}

vm_obj vm_expr_pos(vm_obj const & provider_obj, vm_obj const & expr_obj) {
    pos_info_provider const & provider = to_pos_info_provider(provider_obj);
    auto opt_pos_info = provider.get_pos_info(to_expr(expr_obj));
    if (opt_pos_info) {
        std::cout << opt_pos_info->first << opt_pos_info->second << std::endl;
        return mk_vm_some(to_obj(*opt_pos_info));
    } else {
        std::cout << "none" << std::endl;
        return mk_vm_none();
    }
}

void initialize_vm_pos_info_provider() {
    DECLARE_VM_BUILTIN(name({"pos_info_provider", "expr_pos"}), vm_expr_pos);
}

void finalize_vm_pos_info_provider() {}
}

