/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch, Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {

void* get_internal_ptr(vm_obj const & o);

template<typename T>
T * get_vm_ptr(vm_obj const & ptr) {
    return (T*)get_internal_ptr(ptr);
}

void initialize_vm_ptr();
void finalize_vm_ptr();
}
