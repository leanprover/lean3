/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include <memory>
#include "kernel/type_checker.h"
#include "library/util.h"

namespace lean {
enum class extern_status { External, NotExternal };
/** \brief Mark the definition named \c n as extern or not.

    The method throws an exception if \c n is
      - not a definition
      - a theorem
      - an opaque definition that was not defined in main module

    "extern" definitions can be freely unfolded by automation (i.e., elaborator, simplifier, etc).
    We should view it as a hint to automation.
*/
environment set_extern(environment const & env, name const & n, extern_status s, name const & ns, bool persistent);

extern_status get_extern_status(environment const & env, name const & n);

inline bool is_extern(environment const & env, name const & n) { return get_extern_status(env, n) == extern_status::External; }

/* \brief Execute the given function for each declaration explicitly marked with a reducibility annotation */
void for_each_extern(environment const & env, std::function<void(name const &, extern_status)> const & fn);

// /** \brief Create a predicate that returns true for all non extern constants in \c env */
name_predicate mk_not_extern_pred(environment const & env);

void initialize_extern();
void finalize_extern();
}
