/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
pos_info to_pos_info_provider(vm_obj const & o);
vm_obj to_obj(pos_info_provider const & p);

void initialize_vm_pos_info_provider();

void finalize_vm_pos_info_provider();
}
