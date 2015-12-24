/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/simplifier/simplifier.h"

namespace lean {
namespace blast {
namespace arith {

pair<simp::result, list<expr> > normalize(expr const & e, expr const & type);
pair<expr, list<expr> > normalize_prove_eq(expr const & e1, expr const & e2, expr const & type);

}

void initialize_normalize();
void finalize_normalize();

}}
