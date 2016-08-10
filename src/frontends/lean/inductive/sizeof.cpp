/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/environment.h"
#include "frontends/lean/inductive/sizeof.h"

namespace lean {

environment mk_basic_sizeof(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

environment mk_derived_sizeof(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

environment mk_has_sizeof(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

environment mk_basic_sizeof_spec_lemmas(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

environment mk_derived_sizeof_spec_lemmas(environment const & env, name const & ind_name) {
     throw exception("TODO(dhs): implement");
}

void initialize_inductive_sizeof() {}
void finalize_inductive_sizeof() {}
}
