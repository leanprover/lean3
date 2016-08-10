/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"

namespace lean {

/** \brief Given a basic inductive datatype `I` in `env`, add `I.c.injective`
    to the environment for each intro rule of `I`. */
environment mk_basic_injective(environment const & env, name const & ind_name);

/** \brief Given a derived inductive datatype `I` in `env` with parent `J`,
    add `I.c.injective` to the environment for each intro rule of `I`.

    \remark I.c.injective := pack . J.c.injective . unpack. */
environment mk_derived_injective(environment const & env, name const & ind_name);

void initialize_inductive_injective();
void finalize_inductive_injective();

}
