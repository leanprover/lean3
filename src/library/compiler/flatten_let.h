/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
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

expr flatten_let(environment const & env, expr const & e);

}
