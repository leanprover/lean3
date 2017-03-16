/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <iostream>
#include "library/io_state.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_io.h"
#include "util/process.h"

namespace lean {

struct vm_process : public vm_external {
    process m_val;
    vm_process(process v):m_val(v) {}
    virtual ~vm_process() {}
    virtual void dealloc() override {
        this->~vm_process();
        get_vm_allocator().deallocate(sizeof(vm_process), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {
        return new vm_process(m_val);
    }

    virtual vm_external * clone(vm_clone_fn const &) override {
        return new (get_vm_allocator().allocate(sizeof(vm_process))) vm_process(m_val);
    }
};

bool is_process(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_process*>(to_external(o));
}

process & to_process(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_process*>(to_external(o)));
    return static_cast<vm_process*>(to_external(o))->m_val;
}

vm_obj to_obj(vm_process const & e) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_process))) vm_process(e));
}

vm_obj process_builder_new(vm_obj const & string_obj, vm_obj const &) {
    auto command = to_string(string_obj);
    process proc = process(command);
    return mk_io_result(to_obj(proc));
}

vm_obj process_builder_run(vm_obj const & builder_obj, vm_obj const &) {
    process & builder = to_process(builder_obj);
    builder.run();
    return mk_io_result(mk_vm_unit());
}

vm_obj process_builder_arg(vm_obj const & builder_obj, vm_obj const & arg_obj, vm_obj const &) {
    process & proc = to_process(builder_obj);
    auto arg = to_string(arg_obj);
    proc.arg(arg);
    return mk_io_result(mk_vm_unit());
}

void initialize_vm_process() {
    DECLARE_VM_BUILTIN(name({"process", "builder", "new"}),  process_builder_new);
    DECLARE_VM_BUILTIN(name({"process", "builder", "run"}),  process_builder_run);
    DECLARE_VM_BUILTIN(name({"process", "builder", "arg"}),  process_builder_arg);
}

void finalize_vm_process() {
}
}
