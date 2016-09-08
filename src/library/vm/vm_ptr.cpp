/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch, and Leonardo de Moura
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_ptr.h"

namespace lean {

// An object representing pointers to C compatible structs.
struct vm_ptr : public vm_external {
protected:
    virtual void dealloc() {
        this->~vm_ptr(); get_vm_allocator().deallocate(sizeof(vm_ptr), this);
    }
    friend vm_obj_cell;
public:
    void *  m_pointer;
    vm_obj m_destructor;

    ~vm_ptr() {}
    vm_ptr(void* data, vm_obj const & d) : vm_external(), m_pointer(data), m_destructor(d) {}
    vm_ptr(const vm_ptr & other) : vm_external() {
        m_pointer = other.m_pointer;
        m_destructor = other.m_destructor;
    }

    vm_ptr(vm_ptr * other) : vm_external() {
        m_pointer = other->m_pointer;
        m_destructor = other->m_destructor;
    }
};

class vm_child_ptr : public vm_ptr {
    vm_obj m_parent;
public:
    vm_child_ptr(void* data, vm_obj destructor, vm_obj const & parent)
        : vm_ptr(data, destructor), m_parent(parent) {}
};

struct vm_array {
    unsigned m_len;
    unsigned m_capacity;
    char m_data[0];

    vm_array(int capacity) : m_len(0), m_capacity(capacity) {}

    void* index(unsigned offset) {
        return (void*)(m_data + offset);
    }
};

vm_obj mk_vm_ptr(void * data, vm_obj destructor) {
    return vm_obj(new (get_vm_allocator().allocate(sizeof(vm_ptr))) vm_ptr(data, destructor));
}

vm_obj mk_vm_child_ptr(void * data, vm_obj destructor, vm_obj parent) {
    return vm_obj(new (get_vm_allocator().allocate(sizeof(vm_child_ptr))) vm_child_ptr(data, destructor, parent));
}

inline vm_ptr * to_ptr(vm_obj_cell * o) {
    lean_assert(is_external(o));
    return static_cast<vm_ptr*>(o);
}

vm_obj index_vm_array(vm_obj const & base, size_t off) {
    vm_array* array = (vm_array*)(to_ptr(&*base)->m_pointer);
    lean_assert(array);
    auto element_ptr = (void*)(array->m_data + off);
    return mk_vm_child_ptr(element_ptr, mk_vm_simple(0), base);
}

void* to_void_ptr(vm_obj const & o) {
    return to_ptr(&*o)->m_pointer;
}

vm_obj allocate_sized(vm_obj const &, vm_obj const &, vm_obj const & size, vm_obj const & destructor, vm_obj const &) {
    auto no_bytes = to_unsigned(size);
    void * data = malloc(sizeof(char) * no_bytes);
    return mk_vm_ptr(data, destructor);
}

vm_obj allocate_array(vm_obj const &, vm_obj const &, vm_obj const & elem_size, vm_obj const & initial_capacity, vm_obj const & destructor, vm_obj const &) {
    unsigned type_size = to_unsigned(elem_size);
    unsigned init_cap = to_unsigned(initial_capacity);

    vm_array * data =
        (vm_array*)(malloc(sizeof(vm_array) + (sizeof(char) * type_size * init_cap)));
    *data = vm_array(init_cap);
    return mk_vm_ptr((vm_array*)data, destructor);
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

vm_obj index_array(vm_obj const & type,
                   vm_obj const & array,
                   vm_obj const & index,
                   vm_obj const &) {
    // throw "hello world";
    unsigned idx = to_unsigned(index);
    vm_obj size_of = mk_native_closure(
         get_vm_state().env(),
         name{"ffi", "sizeof"},
         {});
    unsigned type_size = to_unsigned(invoke(size_of, type, mk_vm_simple(0)));
    size_t off = (idx * type_size);
    return index_vm_array(array, off);
}

void* pointer_from_vm_array(vm_obj const & array) {
    return (void*)((to_raw_ptr<vm_array>(array))->m_data);
}

// would be cool if we could model the arrays in the IR
// depending on what typing rules we select a piece of
// code is roughly
// struct array { unsigned cap; unsigned len; char data[0]; }
// or with a more expressive type system (dependent record style).
// struct array { unsigned cap; unsigned len; char data[cap] }
vm_obj array_capacity(vm_obj const &, vm_obj const & array, vm_obj const &) {
    auto arr = to_raw_ptr<vm_array>(array);
    int *cap = new int;
    *cap = arr->m_capacity;
    return mk_vm_child_ptr(cap, mk_vm_simple(0), array);
}

vm_obj array_length(vm_obj const &, vm_obj const & array, vm_obj const &) {
    auto arr = to_raw_ptr<vm_array>(array);
    int *len = new int;
    *len = arr->m_len;
    return mk_vm_child_ptr(len, mk_vm_simple(0), array);
}

void initialize_vm_ptr() {
    // Allocation primitives
    DECLARE_VM_BUILTIN(name({"ffi", "allocate_sized"}), allocate_sized);
    DECLARE_VM_BUILTIN(name({"ffi", "allocate_array"}), allocate_array);
    DECLARE_VM_BUILTIN(name({"ffi", "array_length"}), array_length);
    DECLARE_VM_BUILTIN(name({"ffi", "array_capacity"}), array_capacity);
    DECLARE_VM_BUILTIN(name({"ffi", "base_size_of"}), base_size_of);
    DECLARE_VM_BUILTIN(name({"ffi", "write_nat_as_int"}), write_nat_as_int);
    DECLARE_VM_BUILTIN(name({"ffi", "read_int_as_nat"}), read_int_as_nat);
    DECLARE_VM_BUILTIN(name({"ffi", "write_char_as_char"}), write_char_as_char);
    DECLARE_VM_BUILTIN(name({"ffi", "read_char_as_char"}), read_char_as_char);
    // Array access
    DECLARE_VM_BUILTIN(name({"ffi", "index_array"}), index_array);
}

void finalize_vm_ptr() {
}
}
