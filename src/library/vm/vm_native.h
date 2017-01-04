/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include "library/vm/vm_expr.h"

namespace lean {

vm_obj deserialize_quoted_expr(std::string data);

void initialize_vm_native();
void finalize_vm_native();
}
