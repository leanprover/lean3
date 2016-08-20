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

// An object representing pointers to C compatible structs.
struct vm_ptr : public vm_obj_cell {
protected:
    virtual void dealloc() {
        this->~vm_ptr(); get_vm_allocator().deallocate(sizeof(vm_ptr), this);
    }
    friend vm_obj_cell;
public:
    void *  m_pointer;
    vm_obj m_destructor;

    ~vm_ptr() {}
    vm_ptr(void* data, vm_obj const & d) : vm_obj_cell(vm_obj_kind::Pointer), m_pointer(data), m_destructor(d) {}
    vm_ptr(const vm_ptr & other) : vm_obj_cell(vm_obj_kind::Pointer) {
        m_pointer = other.m_pointer;
        m_destructor = other.m_destructor;
    }

    vm_ptr(vm_ptr * other) : vm_obj_cell(vm_obj_kind::Pointer) {
        m_pointer = other->m_pointer;
        m_destructor = other->m_destructor;
    }

};

vm_obj mk_vm_ptr(void * data, vm_obj destructor) {
    return vm_obj(new (get_vm_allocator().allocate(sizeof(vm_ptr))) vm_ptr(data, destructor));
}

inline vm_ptr * to_ptr(vm_obj_cell * o) { /* lean_assert(is_(o)); */ return static_cast<vm_ptr*>(o); }

vm_obj offset(vm_obj const & base, size_t off) {
        char* base_ptr = (char*)(to_ptr(&*base)->m_pointer);
        auto element_ptr = (void*)(base_ptr + off);
        return mk_vm_ptr(element_ptr, mk_vm_simple(0));
}

void* to_void_ptr(vm_obj const & o) {
    return to_ptr(&*o)->m_pointer;
}

vm_obj allocate_ptr(vm_obj const &, vm_obj const & size, vm_obj const & proof, vm_obj const & destructor, vm_obj const &) {
    auto no_bytes = to_unsigned(size);
    void * data = (void*)malloc(sizeof(char) * no_bytes);
    return mk_vm_ptr(data, destructor);
}

vm_obj write_nat_as_int(vm_obj const & nat, vm_obj const & int_ptr, vm_obj const &) {
    // This needs to be carefull thought about before shipping, casting
    // semantics are hard to get right.
    unsigned value = to_unsigned(nat);
    int as_int = (int)value;

    int * iptr = (int*)to_ptr(int_ptr)->m_pointer;
    *iptr = as_int;

    return mk_vm_unit();
}

vm_obj read_int_as_nat(vm_obj const & int_ptr, vm_obj const &) {
    int * iptr = (int*)to_ptr(int_ptr)->m_pointer;
    int i = *iptr;
    return mk_vm_nat((unsigned) i);
}

vm_obj write_char_as_char(vm_obj const & c, vm_obj const & char_ptr, vm_obj const &) {
    // This needs to be carefull thought about before shipping, casting
    // semantics are hard to get right.
    unsigned value = to_unsigned(c);
    char as_char = (char)value;

    char * cptr = (char*)to_ptr(char_ptr)->m_pointer;
    *cptr = as_char;

    return mk_vm_unit();
}

vm_obj read_char_as_char(vm_obj const & char_ptr, vm_obj const &) {
    char * cptr = (char*)to_ptr(char_ptr)->m_pointer;
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

vm_obj index_array(vm_obj const & n,
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
    size_t off = (idx * type_size);
    return offset(array, off);
}

void initialize_vm_ptr() {
    DECLARE_VM_BUILTIN(name({"ffi", "allocate"}), allocate_ptr);
    DECLARE_VM_BUILTIN(name({"ffi", "base_size_of"}), base_size_of);
    DECLARE_VM_BUILTIN(name({"ffi", "write_nat_as_int"}), write_nat_as_int);
    DECLARE_VM_BUILTIN(name({"ffi", "read_int_as_nat"}), read_int_as_nat);
    DECLARE_VM_BUILTIN(name({"ffi", "write_char_as_char"}), write_char_as_char);
    DECLARE_VM_BUILTIN(name({"ffi", "read_char_as_char"}), read_char_as_char);
    DECLARE_VM_BUILTIN(name({"ffi", "index_array"}), index_array);
}

void finalize_vm_ptr() {
}
}
