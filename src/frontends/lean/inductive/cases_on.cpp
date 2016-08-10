/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/inductive/cases_on.h"

namespace lean {

environment mk_derived_cases_on(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

void initialize_inductive_cases_on() {}
void finalize_inductive_cases_on() {}
}
