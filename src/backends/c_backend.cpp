    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <utility>
#include "c_backend.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/instantiate.h"
#include "used_names.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {

c_backend::c_backend(environment const & env, optional<std::string> main_fn)
    : backend(env, main_fn) {}

void mangle_name(std::ostream& os, name const & n) {
    os << n;
}

void c_backend::generate_code(optional<std::string> output_path) {
    std::fstream fs("out.c", std::ios_base::out);
    for (auto proc : this->m_procs) {
        this->generate_proc(fs, proc);
        fs << std::endl;
    }
    fs.flush();
    fs.close();
}

void c_backend::generate_proc(std::ostream& os, proc const & p) {
    os << "Object " << p.m_name << "(";

    auto comma = false;

    for (auto arg : p.m_args) {
        if (comma) {
            os << ", ";
        } else {
            comma = true;
        }
        os << "Object ";
        mangle_name(os, arg);
    }

    os << ") {" << std::endl;

    this->generate_simple_expr(os, *p.m_body);

    os << std::endl << "}" << std::endl;
}

void c_backend::generate_simple_expr_var(std::ostream& os, simple_expr const & se) {
    auto n = var_name(se);
    mangle_name(os, n);
}

void c_backend::generate_simple_expr_error(std::ostream& os, simple_expr const & se) {
    // auto n = var_name(se);
    // mangle_name(os, n);
    os << "error(msg)";
}

void c_backend::generate_simple_expr_call(std::ostream& os, simple_expr const & se) {
    // auto n = var_name(se);
    // mangle_name(os, n);
    os << "call(args)";
}

void c_backend::generate_binding(std::ostream& os, pair<name, shared_ptr<simple_expr>> & p) {
    auto n = p.first;
    auto se = p.second;

    os << "Object ";
    mangle_name(os, n);
    os << " = ";
    this->generate_simple_expr(os, *se);
    os << ";" << std::endl;
}

void c_backend::generate_simple_expr_let(std::ostream& os, simple_expr const & se) {
    auto bindings = to_simple_let(&se)->m_bindings;
    auto body = to_simple_let(&se)->m_body;
    for (auto binding : bindings) {
        this->generate_binding(os, binding);
    }
    this->generate_simple_expr(os, *body);
}

void c_backend::generate_simple_expr(std::ostream& os, simple_expr const & se) {
    switch (se.kind()) {
        case simple_expr_kind::SVar:
            generate_simple_expr_var(os, se);
            break;
        case simple_expr_kind::Call:
            generate_simple_expr_call(os, se);
            break;
        case simple_expr_kind::Let:
            generate_simple_expr_let(os, se);
            break;
        case simple_expr_kind::Error:
            generate_simple_expr_error(os, se);
            break;
    }
}

}
