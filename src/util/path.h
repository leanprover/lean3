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

std::string normalize_path_string(std::string f);
bool is_path_sep_dup(char c);
char path_sep();

// A platform independent abstraction over file system paths.
class path {
    std::vector<std::string> m_components;
    // TODO: properly support relative vs. absolute
    bool m_absolute;
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

}
