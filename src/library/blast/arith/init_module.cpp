/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/arith/acl.h"
#include "library/blast/arith/num.h"

namespace lean {
namespace blast {

void initialize_arith_module() {
    initialize_acl();
    initialize_num();
}

void finalize_arith_module() {
    finalize_num();
    finalize_acl();
}
}}
