/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include "library/vm/vm_expr.h"

namespace lean {

typedef std::tuple<std::string, std::string> native_symbol;

typedef std::vector<native_symbol> native_symbol_seq;

// The type signature of a native library initializer.
typedef native_symbol_seq (*native_library_initializer)();

// Returns a `vm_obj` representing the serialized expression in data.
vm_obj deserialize_quoted_expr(std::string data);

void initialize_vm_native();
void finalize_vm_native();
}
