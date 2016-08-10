/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "frontends/lean/inductive/inductive_cmds.h"
#include "frontends/lean/inductive/sizeof.h"
#include "frontends/lean/inductive/injective.h"
#include "frontends/lean/inductive/cidx.h"

namespace lean {
void initialize_frontend_inductive_module() {
    initialize_inductive_cmds();
    initialize_inductive_sizeof();
    initialize_inductive_injective();
    initialize_inductive_cidx();
}

void finalize_frontend_inductive_module() {
    finalize_inductive_injective();
    finalize_inductive_sizeof();
    finalize_inductive_cidx();
}
}
