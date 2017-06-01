/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Mario Carneiro
*/
#include <vector>
#include "library/vm/vm.h"
#include "library/trace.h"

#define lean_cached_trace(CODE) lean_trace(name({"cached", "update"}), CODE)

namespace lean {
struct vm_cached : public vm_external {
    vm_obj m_default;
    vm_obj m_value;
    vm_cached(vm_obj const & def, vm_obj const & v):m_default(def), m_value(v) {}
    virtual ~vm_cached() {}
    virtual void dealloc() override { this->~vm_cached(); get_vm_allocator().deallocate(sizeof(vm_cached), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_cached(m_default, m_value); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_cached))) vm_cached(m_default, m_value); }
};

vm_obj const & get_cached_default(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_cached*>(to_external(o)));
    return static_cast<vm_cached*>(to_external(o))->m_default;
}

vm_obj const & get_cached_value(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_cached*>(to_external(o)));
    return static_cast<vm_cached*>(to_external(o))->m_value;
}

vm_obj const & set_cached_value(vm_obj const & o, vm_obj const & v) {
    lean_vm_check(dynamic_cast<vm_cached*>(to_external(o)));
    return static_cast<vm_cached*>(to_external(o))->m_value = v;
}

vm_obj cached_mk(vm_obj const &, vm_obj const & def, vm_obj const & v) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_cached))) vm_cached(def, v));
}

vm_obj cached_update(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const & c, vm_obj const & v, vm_obj const & fn) {
    lean_cached_trace(tout() << "cached update\n";);
    set_cached_value(c, v);
    return invoke(fn, mk_vm_unit());
}

vm_obj cached_val(vm_obj const &, vm_obj const &, vm_obj const & c) {
    return get_cached_value(c);
}

unsigned cached_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    data.push_back(get_cached_value(o));
    return 0;
}

void initialize_vm_cached() {
    DECLARE_VM_BUILTIN(name({"cached", "mk'"}),              cached_mk);
    DECLARE_VM_BUILTIN(name({"cached", "val"}),              cached_val);
    DECLARE_VM_BUILTIN(name({"cached", "update"}),           cached_update);
    DECLARE_VM_CASES_BUILTIN(name({"cached", "cases_on"}),   cached_cases_on);
}

void finalize_vm_cached() {
}
}
