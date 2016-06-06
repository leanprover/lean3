/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include "kernel/environment.h"
#include "config.h"

namespace lean {
enum native_compiler_mode { JIT, AOT };
void native_compile(environment const & env, config & conf, buffer<pair<name, expr>> & procs);
void native_compile(environment const & env, config & conf, declaration const & d, native_compiler_mode mode);
void initialize_native_compiler();
void finalize_native_compiler();
}
