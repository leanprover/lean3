/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Mario Carneiro
*/
#pragma once

#include "library/vm/vm.h"

namespace lean {
void initialize_vm_cached();
void finalize_vm_cached();
}
