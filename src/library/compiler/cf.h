/*

Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Annotate locations where control flow of a function exits.

    Example: given, the definition below

    TODO

    We will generate an

    TODO
*/

bool is_initialize(expr const & e) {
    return mk_constant(name({"native_compiler", "initialize"})) == e;
}

bool is_uninitialized(expr const & e) {
    return mk_constant(name({"native_compiler", "uninitialized"})) == e;
}

bool is_store(expr const & e) {
    return mk_constant(name({"native_compiler", "store"})) == e;
}

expr cf(environment const & env, expr const & e);
}
