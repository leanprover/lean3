/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch, and Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "library/compiler/options.h"

#ifndef LEAN_DEFAULT_NATIVE_LIBRARY_PATH
#define LEAN_DEFAULT_NATIVE_LIBRARY_PATH ""
#endif
#ifndef LEAN_DEFAULT_NATIVE_MAIN_FN
#define LEAN_DEFAULT_NATIVE_MAIN_FN "main"
#endif
#ifndef LEAN_DEFAULT_NATIVE_INCLUDE_PATH
#define LEAN_DEFAULT_NATIVE_INCLUDE_PATH ""
#endif
#ifndef LEAN_DEFAULT_NATIVE_EMIT_DWARF
#define LEAN_DEFAULT_NATIVE_EMIT_DWARF false
#endif

namespace lean {
namespace native {
/* Options */
static name * g_native_library_path    = nullptr;
static name * g_native_main_fn         = nullptr;
static name * g_native_include_path    = nullptr;
static name * g_native_emit_dwarf      = nullptr;

char const * get_native_library_path(options const & o) {
    return o.get_string(*g_native_library_path, LEAN_DEFAULT_NATIVE_LIBRARY_PATH);
}

char const * get_native_main_fn(options const & o) {
    return o.get_string(*g_native_main_fn, LEAN_DEFAULT_NATIVE_MAIN_FN);
}

char const * get_native_include_path(options const & o) {
    return o.get_string(*g_native_include_path, LEAN_DEFAULT_NATIVE_INCLUDE_PATH);
}

bool get_native_emit_dwarf(options const & o) {
    return o.get_bool(*g_native_emit_dwarf, LEAN_DEFAULT_NATIVE_EMIT_DWARF);
}

config::config(options const & o) {
    m_native_library_path = get_native_library_path(o);
    m_native_main_fn      = get_native_main_fn(o);
    m_native_include_path = get_native_include_path(o);
    m_native_emit_dwarf   = get_native_emit_dwarf(o);
}

LEAN_THREAD_PTR(config, g_native_config);

scope_config::scope_config(options const & o):
    m_old(g_native_config),
    m_config(o) {
    g_native_config = &m_config;
}

scope_config::~scope_config() {
    g_native_config = m_old;
}

config & get_config() {
    lean_assert(g_native_config);
    return *g_native_config;
}

void initialize_options() {
    g_native_library_path = new name{"native", "library_path"};
    g_native_main_fn      = new name{"native", "main"};
    g_native_include_path = new name{"native", "include_path"};
    g_native_emit_dwarf   = new name{"native", "emit_dwarf"};

    register_string_option(*native::g_native_library_path, LEAN_DEFAULT_NATIVE_LIBRARY_PATH,
                         "(native_compiler) path used to search for native libraries, including liblean");

    register_string_option(*native::g_native_main_fn, LEAN_DEFAULT_NATIVE_MAIN_FN,
        "(native_compiler) definition used as the program entry point");

    register_string_option(*native::g_native_include_path, LEAN_DEFAULT_NATIVE_INCLUDE_PATH,
        "(native_compiler) path used to search for native headers, for example those included with Lean");

    register_bool_option(*native::g_native_emit_dwarf, LEAN_DEFAULT_NATIVE_EMIT_DWARF,
        "(native_compiler) flag controls whether dwarf debugging information is generated for the emitted code");
}

void finalize_options() {
    delete g_native_library_path;
    delete g_native_main_fn;
    delete g_native_include_path;
    delete g_native_emit_dwarf;
}
}}
