/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include "kernel/declaration.h"
#include "util/sexpr/options.h"

namespace lean {


void lint_declaration(environment const &, declaration const & decl);
bool linting_enabled(options const & opts);
void initialize_linter();
void finalize_linter();

}
