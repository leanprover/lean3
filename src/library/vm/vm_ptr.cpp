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
    void *  m_pointer;
    vm_obj m_destructor;
    vm_ptr(void* data, vm_obj const & d):m_pointer(pointer), m_destructor(d) {}
    vm_ptr(const vm_ptr & other) : vm_external(other) {
        m_pointer = other.m_data;
        m_destructor = other.m_destructor;
    }
    ~vm_ptr() {
        // std::cout << "running the destructor" << std::endl;
    }
    virtual void dealloc() override {
        this->~vm_ptr(); get_vm_allocator().deallocate(sizeof(vm_ptr), this);
    }
};

vm_ptr const & to_vm_ptr(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_ptr*>(to_external(o)));
    return *static_cast<vm_ptr*>(to_external(o));
}

void* get_internal_ptr(vm_obj const & o) {
    auto ptr = to_vm_ptr(o);
    return ptr.m_pointer;
}

vm_obj to_obj(vm_ptr const & ptr) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_ptr))) vm_ptr(ptr));
}

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

    int * iptr = (int*)to_vm_ptr(int_ptr).m_pointer;
    *iptr = as_int;

    return mk_vm_unit();
}

vm_obj read_int_as_nat(vm_obj const & int_ptr, vm_obj const &) {
    int * iptr = (int*)to_vm_ptr(int_ptr).m_pointer;
    int i = *iptr;
    return mk_vm_nat((unsigned) i);
}

vm_obj write_char_as_char(vm_obj const & c, vm_obj const & char_ptr, vm_obj const &) {
    // This needs to be carefull thought about before shipping, casting
    // semantics are hard to get right.
    unsigned value = to_unsigned(c);
    char as_char = (char)value;

    char * cptr = (char*)to_vm_ptr(char_ptr).m_pointer;
    *cptr = as_char;

    return mk_vm_unit();
}

vm_obj read_char_as_char(vm_obj const & char_ptr, vm_obj const &) {
    char * cptr = (char*)to_vm_ptr(char_ptr).m_data;
    char c = *cptr;
    return mk_vm_nat((unsigned) c);
}

vm_obj base_size_of(vm_obj const & base_type) {
    auto ci = cidx(base_type);
    switch (ci) {
        case 0:
            return mk_vm_nat(sizeof(int));
        case 1:
            return mk_vm_nat(sizeof(char));
        default:
            // TODO: throw a proper error
            throw std::runtime_error("pattern match fail");
    }
}

vm_obj fold_io_array(vm_obj const & size,
                     vm_obj const & array,
                     vm_obj const & init,
                     vm_obj const & f,
                     vm_obj const & last) {
    char *c = (char*)get_internal_ptr(array);
    while (*c != '\0') {
        std::cout << c << std::endl;
        c += 1;
    }
    return mk_vm_simple(0);
}

vm_obj read_array(vm_obj const & n,
                  vm_obj const & type,
                  vm_obj const & array,
                  vm_obj const & index,
                  vm_obj const &) {
    unsigned idx = to_unsigned(index);
    vm_obj size_of = mk_native_closure(
        get_vm_state().env(),
        name{"ffi", "sizeof"},
        {});
    unsigned type_size = to_unsigned(invoke(size_of, type));

    char* base = (char*)get_internal_ptr(array);
    char* element = base + (idx * type_size);

    vm_ptr element_ptr = vm_ptr(to_vm_ptr(array));
    element_ptr.m_pointer = (void*)element;

    return to_obj(element_ptr);
}

vm_obj write_array(vm_obj const & n,
                   vm_obj const & type,
                   vm_obj const & array,
                   vm_obj const & index,
                   vm_obj const & value,
                   vm_obj const &) {
    unsigned idx = to_unsigned(index);
    vm_obj size_of = mk_native_closure(
        get_vm_state().env(),
        name{"ffi", "sizeof"},
        {});
    unsigned type_size = to_unsigned(invoke(size_of, type));

    char* base = (char*)get_internal_ptr(array);
    char* element = base + (idx * type_size);

    void* element_to_store = get_internal_ptr(value);
    std::cout << (*(char*)element_to_store) << std::endl;
    memcpy((void*)element, element_to_store, type_size);

    return mk_vm_unit();
}

void initialize_vm_ptr() {
    DECLARE_VM_BUILTIN(name({"ffi", "allocate"}), allocate_ptr);
    DECLARE_VM_BUILTIN(name({"ffi", "base_size_of"}), base_size_of);
    DECLARE_VM_BUILTIN(name({"ffi", "ptr_to_string"}), ptr_to_string);
    DECLARE_VM_BUILTIN(name({"ffi", "write_nat_as_int"}), write_nat_as_int);
    DECLARE_VM_BUILTIN(name({"ffi", "read_int_as_nat"}), read_int_as_nat);
    DECLARE_VM_BUILTIN(name({"ffi", "write_char_as_char"}), write_char_as_char);
    DECLARE_VM_BUILTIN(name({"ffi", "read_char_as_char"}), read_char_as_char);
    DECLARE_VM_BUILTIN(name({"ffi", "read_array"}), read_array);
    DECLARE_VM_BUILTIN(name({"ffi", "write_array"}), write_array);
    DECLARE_VM_BUILTIN(name({"ffi", "fold_io_array"}), fold_io_array);
}

void finalize_vm_ptr() {
}
}
