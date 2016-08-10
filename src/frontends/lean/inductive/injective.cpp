/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/environment.h"
#include "frontends/lean/inductive/injective.h"

namespace lean {

environment mk_basic_injective(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

environment mk_derived_injective(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

void initialize_inductive_injective() {}
void finalize_inductive_injective() {}
}
