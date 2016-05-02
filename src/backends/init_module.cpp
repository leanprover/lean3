/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/

#include <iostream>
#include "library/trace.h"

namespace lean {

void initialize_backends_module() {
    // std::cout << "init backend" << std::endl;
    register_trace_class("backend");
    register_trace_class({"backend", "compile"});
    register_trace_class("c_backend");
}

void finalize_backends_module() {
    // std::cout << "finalize backend" << std::endl;
}
}
