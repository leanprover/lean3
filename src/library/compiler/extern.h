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

environment set_extern(environment const & env, name const & n, extern_status s, name const & ns, bool persistent);

extern_status get_extern_status(environment const & env, name const & n);

inline bool is_extern(environment const & env, name const & n) {
    return get_extern_status(env, n) == extern_status::External;
}

void for_each_extern(environment const & env, std::function<void(name const &, extern_status)> const & fn);

void initialize_extern();
void finalize_extern();

}
