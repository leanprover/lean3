/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "frontends/lean/inductive/inductive_cmds.h"

namespace lean {
void initialize_frontend_inductive_module() {
    initialize_inductive_cmds();
}

void finalize_frontend_inductive_module() {
    finalize_inductive_cmds();
}
}
