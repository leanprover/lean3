/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/explicit.h"

namespace lean {

expr unelaborate(environment const & env, list<expr> const & ctx, expr const & e);

}
