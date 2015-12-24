/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/trace.h"
#include "library/blast/arith/heuristic.h"
#include "library/blast/arith/num.h"
#include "library/blast/arith/normalize.h"

namespace lean {
namespace blast {

void initialize_arith_module() {
    register_trace_class(name("blast", "arith"));
    initialize_num();
    initialize_normalize();
    initialize_heuristic();
}

void finalize_arith_module() {
    finalize_heuristic();
    finalize_normalize();
    finalize_num();
}
}}
