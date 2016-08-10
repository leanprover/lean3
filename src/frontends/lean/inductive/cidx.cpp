/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/environment.h"
#include "frontends/lean/inductive/cidx.h"

namespace lean {

/** \brief Given a basic inductive datatype `I` in `env`, add `I.cidx`. */
environment mk_basic_cidx(environment const & env, name const & ind_name);

/** \brief Given a derived inductive datatype `I` in `env` with parent `J`,
    add `I.cidx`.

    \remark `I.cidx := J.cidx`. */
environment mk_derived_cidx(environment const & env, name const & ind_name);

void initialize_inductive_cidx() {}
void finalize_inductive_cidx() {}
}
