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

    let x := 2
    let y := 2
    in 2 + 2

    We will annotate the final expression with the proper control flow, yielding
    the below program:

    let x := 2
    let y := 2
    in native_compiler.return (2 + 2)
*/

bool is_return_expr(expr const & e);
expr annotate_return(environment const & env, expr const & e);
}
