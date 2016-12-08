/*
Copyright (c) 2016 Jared Roesch All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include <string>
#include <vector>
#include <ostream>
#include "util/name.h"
#include "util/exception.h"
#include "util/path.h"

namespace lean {

// A class which represents a platform-independent sequence of paths, that can
// be searched.
class path_var {
public:
    std::vector<path> m_paths;
    path_var(std::string pv);

    friend std::ostream & operator<<(std::ostream & out, path_var const & pv);
    // template<typename R>
    // iterate(std::function<R(path const &)> for_each) {
    //     for (const & path : m_paths) {
    //         for_each()
    //     }
    // }
};
}
