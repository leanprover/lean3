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

namespace lean {

// a file system path
class path {
    std::vector<std::string> m_components;
public:
    path(std::string p);
    path(char const * p);
    path(path const & p);

    void copy(path const & path);

    path append(path const & path);
    path append(std::string const & path);
    path append(char const * path);

    friend std::ostream & operator<<(std::ostream & out, path const & p);

    std::string to_string() {
        auto str = std::stringstream();
        str << *this;
        return str.str();
    }
};

// a set o file system paths
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
