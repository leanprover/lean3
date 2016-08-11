/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch, and Leonardo de Moura
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_nat.h"

namespace lean {
// =======================================
// Builtin system.ffi.ptr operations

struct vm_ptr : public vm_external {
    void *  m_data;
    vm_obj m_destructor;
    vm_ptr(void* data, vm_obj const & d):m_data(data), m_destructor(d) {}
    ~vm_ptr() {
        std::cout << "running the destructor" << std::endl;
    }
    virtual void dealloc() override { this->~vm_ptr(); get_vm_allocator().deallocate(sizeof(vm_ptr), this); }
};

vm_ptr const & to_vm_ptr(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_ptr*>(to_external(o)));
    return *static_cast<vm_ptr*>(to_external(o));
}

// vm_obj to_obj(backward_lemma_index const & idx) {
//    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_backward_lemmas))) vm_backward_lemmas(idx));
// }

vm_obj allocate_ptr(vm_obj const &, vm_obj const & size, vm_obj const & proof, vm_obj const & destructor, vm_obj const &) {
    auto no_bytes = to_unsigned(size);
    void * data = (void*)malloc(sizeof(char) * no_bytes);
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_ptr))) vm_ptr(data, destructor));
}

vm_obj ptr_to_string(vm_obj const & obj) {
    std::cout << "<ptr>" << std::endl;
    return mk_vm_simple(0);
}

vm_obj write_nat_as_int(vm_obj const & nat, vm_obj const & int_ptr, vm_obj const &) {
    // This needs to be carefull thought about before shipping, casting
    // semantics are hard to get right.
    unsigned value = to_unsigned(nat);
    int as_int = (int)value;

    int * iptr = (int*)to_vm_ptr(int_ptr).m_data;
    *iptr = as_int;

    return mk_vm_unit();
}

vm_obj read_int_as_nat(vm_obj const & int_ptr, vm_obj const &) {
    int * iptr = (int*)to_vm_ptr(int_ptr).m_data;
    int i = *iptr;
    return mk_vm_nat((unsigned) i);
}

void initialize_vm_ptr() {
    DECLARE_VM_BUILTIN(name({"ffi", "allocate"}), allocate_ptr);
    DECLARE_VM_BUILTIN(name({"ffi", "ptr_to_string"}), ptr_to_string);
    DECLARE_VM_BUILTIN(name({"ffi", "write_nat_as_int"}), write_nat_as_int);
    DECLARE_VM_BUILTIN(name({"ffi", "read_int_as_nat"}), read_int_as_nat);
}

void finalize_vm_ptr() {
}
}
