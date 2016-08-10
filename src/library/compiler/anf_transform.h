/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
/** \brief Transform the term into a ANF-like form, where each binding only
    only contains a simple expression.

    Example: given, the definition below

    f (g x y) (w (m x) (n y))

    We will generate:

    let tmp1 := n y in
    let tmp2 := m x in
    let tmp3 := w tmp1 tmp2 in
    let tmp4 := g x y in
    f tmp4 tmp3
*/

bool is_cases_on(environment const & env, expr const & e);

expr anf_transform(environment const & env, expr const & e);

}
