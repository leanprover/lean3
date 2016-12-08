/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, and Jared Roesch
*/
#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#include <windows.h>
#endif
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
#include "util/realpath.h"
#include "util/path.h"

#ifndef LEAN_DEFAULT_MODULE_FILE_NAME
#define LEAN_DEFAULT_MODULE_FILE_NAME "default"
#endif

namespace lean {


#if defined(LEAN_EMSCRIPTEN)

// emscripten version
static char g_path_sep     = ':';
static char g_sep          = '/';
static char g_bad_sep      = '\\';

static bool is_path_sep(char c) { return c == g_path_sep; }

#elif defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)

// Windows version
static char g_path_sep     = ';';
static char g_path_alt_sep = ':';
static char g_sep          = '\\';
static char g_bad_sep      = '/';

static bool is_path_sep(char c) { return c == g_path_sep || c == g_path_alt_sep; }

#elif defined(__APPLE__)

// OSX version
#include <mach-o/dyld.h>
#include <limits.h>
#include <stdlib.h>

static char g_path_sep     = ':';
static char g_sep          = '/';
static char g_bad_sep      = '\\';

static bool is_path_sep(char c) { return c == g_path_sep; }

#else

// Linux version
#include <unistd.h>
#include <string.h>
#include <limits.h> // NOLINT
#include <stdio.h>

static char g_path_sep     = ':';
static char g_sep          = '/';
static char g_bad_sep      = '\\';

static bool is_path_sep(char c) { return c == g_path_sep; }

#endif

// eventually expose this symbol, after rewriting lean_path.
bool is_path_sep_dup(char c) { return is_path_sep(c); }
char path_sep() { return g_path_sep; }

std::string normalize_path_string(std::string f) {
    for (auto & c : f) {
        if (c == g_bad_sep)
            c = g_sep;
    }
    return f;
}

path::path(char const * p) : path(std::string(p)) {}

path::path(std::string p) : m_absolute(true) {
    auto normalized = normalize_path_string(p);

    unsigned i  = 0;
    unsigned j  = 0;

    unsigned sz = normalized.size();
    for (; j < sz; j++) {
        if (normalized[j] == g_sep) {
            if (j > i)
                m_components.push_back(normalized.substr(i, j - i));
            i = j + 1;
        }
    }

    if (j > i)
        m_components.push_back(normalized.substr(i, j - i));
}

path::path(path const & p) {
    for (auto c : p.m_components) {
        this->m_components.push_back(c);
    }
    this->m_absolute = p.m_absolute;
}

std::ostream & operator<<(std::ostream & os, path const & p) {
    if (p.m_absolute) {
        os << g_sep;
    }

    os << p.m_components[0];

    for (size_t i = 1; i < p.m_components.size(); i++) {
        os << g_sep << p.m_components[i];
    }

    return os;
}

// Copies all of `p`s components into `this`.
void path::copy(path const & p) {
    for (auto c : p.m_components) {
        this->m_components.push_back(c);
    }
}

path path::append(std::string const & p) {
    auto p1 = path(*this);
    auto p2 = path(p);
    p1.copy(p2);
    return p1;
}

path path::append(path const & p) {
    auto p1 = path(*this);
    p1.copy(p);
    return p1;
}

path path::append(char const * p) {
    auto p1 = path(*this);
    auto p2 = path(p);
    p1.copy(p2);
    return p1;
}

}
