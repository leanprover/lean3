/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"

namespace lean {

/** \brief Given a derived inductive datatype `I` in `env` with parent `J`,
    add `I.cases_on`.

    \remark I.cases_on := pack . J.cases_on . unpack. */
environment mk_derived_cases_on(environment const & env, name const & ind_name);

void initialize_inductive_cases_on();
void finalize_inductive_cases_on();
}
