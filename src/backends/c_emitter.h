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

namespace lean  {
    // static const char * LEAN_OBJ_TYPE = "lean::obj";
    // static const char * LEAN_ERR = "lean::runtime_error";

    class c_emitter {
    public:
        std::unique_ptr<std::ostream> m_output_stream;
        c_emitter(std::string output_path);
        void emit_return(simple_expr const & se);
    };
}
