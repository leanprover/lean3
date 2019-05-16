/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <limits>
#include "library/vm/vm.h"

namespace lean {
int to_int(vm_obj const & o);
optional<int> try_to_int(vm_obj const & o);
int force_to_int(vm_obj const & o, int def = std::numeric_limits<int>::max());
long to_long(vm_obj const & o);
optional<long> try_to_long(vm_obj const & o);
long force_to_long(vm_obj const & o, long def = std::numeric_limits<long>::max());
void initialize_vm_int();
void finalize_vm_int();
}
