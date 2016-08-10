/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"

namespace lean {

/** \brief Given a basic inductive datatype `I` in `env`, add `I.sizeof`. */
environment mk_basic_sizeof(environment const & env, name const & ind_name);

/** \brief Given a derived inductive datatype `I` in `env` with parent `J`,
    add `I.c.sizeof` to the environment for each intro rule of `I`.

    \remark `I.c.sizeof := J.c.sizeof`. */
environment mk_derived_sizeof(environment const & env, name const & ind_name);

/** \brief Given any inductive datatype `I` in `env`, add `I.has_sizeof`
    and make it an instance.

    \remark Should only be called on user-facing datatypes. */
environment mk_has_sizeof(environment const & env, name const & ind_name);


/** \brief Given a basic inductive datatype `I` in `env`, add `I.c.sizeof_spec`
    to the environment for each intro rule of `I`. */
environment mk_basic_sizeof_spec_lemmas(environment const & env, name const & ind_name);

/** \brief Given a derived inductive datatype `I` in `env` with parent `J`,
    add `I.c.sizeof_spec` to the environment for each intro rule of `I`.

    \remark `I.c.sizeof_spec := J.c.sizeof_spec`. */
environment mk_derived_sizeof_spec_lemmas(environment const & env, name const & ind_name);

void initialize_inductive_sizeof();
void finalize_inductive_sizeof();
}
