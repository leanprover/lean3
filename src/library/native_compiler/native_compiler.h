/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/vm/vm.h"
#include "util/path.h"

namespace lean {
void initialize_install_path();
path get_install_path();

struct extern_fn {
    bool        m_in_lean_namespace;
    name        m_lean_name;
    std::string m_native_name;

    unsigned m_arity;
    extern_fn(bool in_lean_namespace, name lean_name, std::string native_name, unsigned arity) :
        m_in_lean_namespace(in_lean_namespace),
        m_lean_name(lean_name),
        m_native_name(native_name),
        m_arity(arity) {}

    vm_obj to_obj();
};

optional<extern_fn> get_builtin(name const & n);

enum native_compiler_mode { Module, Executable };
void native_compile_binary(environment const & env, declaration const & d);
void compile_with_external_backend(environment const & env, declaration const & d);

void initialize_native_compiler();
void finalize_native_compiler();
}
