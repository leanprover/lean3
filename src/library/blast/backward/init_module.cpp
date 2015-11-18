/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/backward/init_module.h"
#include "library/blast/backward/backward_rule_set.h"

namespace lean {
namespace blast {

void initialize_backward_module() {
    initialize_backward_rule_set();
}

void finalize_backward_module() {
    finalize_backward_rule_set();
}
}
}
