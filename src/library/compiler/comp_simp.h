/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
pair<environment, expr> apply_comp_simp(environment const & env, name const & decl_name, expr const & e);
void initialize_comp_simp();
void finalize_comp_simp();
}
