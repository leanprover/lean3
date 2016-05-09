/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "kernel/environment.h"
#include "backend.h"
#include "simple_expr.h"
#include "library/trace.h"

namespace lean  {
    void free_vars(expr const & e, buffer<name> & ns);
}
