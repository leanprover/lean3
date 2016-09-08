/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch, Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {

void* to_void_ptr(vm_obj const & o);

template <typename T>
T* to_raw_ptr(vm_obj const & o) {
    return (T*)to_void_ptr(o);
}

void* pointer_from_vm_array(vm_obj const & array);

void initialize_vm_ptr();
void finalize_vm_ptr();
}
