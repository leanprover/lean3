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

void initialize_vm_ptr() {
    DECLARE_VM_BUILTIN(name({"ffi", "allocate"}), allocate_ptr);
    DECLARE_VM_BUILTIN(name({"ffi", "ptr_to_string"}), ptr_to_string);

}

void finalize_vm_ptr() {
}
}
