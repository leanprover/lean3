/*
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <cstdlib>
#include <fstream>
#include <vector>
#include <sys/types.h>
#include <sys/stat.h>
#include <dirent.h>
#include "util/exception.h"
#include "util/sstream.h"
#include "util/name.h"
#include "util/optional.h"
#include "util/path.h"
#include "util/path_var.h"

namespace lean {

path_var::path_var(std::string p) {
    auto normalized = normalize_path(p);

    unsigned i  = 0;
    unsigned j  = 0;

    unsigned sz = normalized.size();
    for (; j < sz; j++) {
        if (is_path_sep(normalized[j])) {
            if (j > i) {
                auto p = path(normalized.substr(i, j - i));
                m_paths.push_back(p);
            }
            i = j + 1;
        }
    }

    if (j > i) {
        auto p = path(normalized.substr(i, j - i));
        m_paths.push_back(p);
    }
}

std::ostream & operator<<(std::ostream & os, path_var const & p) {
    os << p.m_paths[0];
    for (size_t i = 1; i < p.m_paths.size(); i++) {
        os << get_path_sep() << p.m_paths[i];
    }

    return os;
}

}
