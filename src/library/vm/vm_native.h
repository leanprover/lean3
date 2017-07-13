/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include "library/vm/vm_expr.h"

namespace lean {

/* .olean, name, symbol_name, arity */
typedef std::tuple<std::string, name, std::string, unsigned int> native_symbol;

struct native_symbol_seq {
    std::vector<native_symbol> m_vector;
    native_symbol_seq(std::initializer_list<native_symbol> is) : m_vector(is) {}
};

// The type signature of a native library initializer.
typedef native_symbol_seq (*native_library_initializer)();

// Returns a `vm_obj` representing the serialized expression in data.
vm_obj deserialize_quoted_expr(std::string data);

void initialize_vm_native();
void finalize_vm_native();
}
