/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include "library/attribute_manager.h"

namespace lean {
bool has_extern_attribute(environment const & env, name const & d) {
    return has_attribute(env, "extern", d);
}

void initialize_extern_attribute() {
    register_attribute(basic_attribute("extern", "mark a constant as external to Lean"));
}

void finalize_extern_attribute() {
}
}
