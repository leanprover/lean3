    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include "clike_backend.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/instantiate.h"
#include "used_names.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {

static const char * LEAN_OBJ_TYPE = "lean::obj";
static const char * LEAN_ERR = "lean::runtime_error";
static const char * LEAN_FN_PTR_SUFFIX = "_fn_ptr";
static const char * LEAN_MAIN = "___lean__main";
static const char * LEAN_FRESH_N_PREFIX = "__$lean$_$";

clike_backend::clike_backend(environment const & env, config & conf)
    : backend(env, conf), m_return(false) {}

// Not really sure if this is suffcient mangling. I can polish this
// over time, first attempt to is to get a linked executable.
void mangle_name(std::ostream& os, name const & n) {
    if (n == name("main")) {
        os << LEAN_MAIN;
    } else if (n.is_anonymous()) {
        os << "anon_name?";
    } else if (n.is_string()) {
        auto s = n.to_string("_");
        os << s;
    } else if (n.is_numeral()) {
        auto s = n.to_string("_");
        os << LEAN_FRESH_N_PREFIX << s;
    } else {
        lean_unreachable();
    }
}

void mangle_name_fn_ptr(std::ostream& os, name const & n) {
    mangle_name(os, n);
    os << LEAN_FN_PTR_SUFFIX;
}

void clike_backend::generate_code() {
    std::fstream fs("out.cpp", std::ios_base::out);
    c_emitter emitter(fs);

    generate_includes(fs);
    // First generate code for constructors.
    for (auto ctor : this->m_ctors) {
        generate_ctor(fs, ctor);
        fs << std::endl;
    }

    // Generate a declaration for each procedure.
    this->m_procs.for_each([&] (name const &n, proc const & p) {
        this->generate_decl(fs, p);
        fs << std::endl;
    });

    // Then generate code for procs.
    this->m_procs.for_each([&] (name const &n, proc const & p) {
        this->generate_proc(fs, p);
        fs << std::endl;
    });

    // Finally generate the shim for main.
    generate_main(fs, this->m_conf.m_main_fn);
    fs.flush();
}

void clike_backend::generate_ctor(std::ostream& os, ctor const & c) {
    if (c.m_arity == 0) {
        os << "static ";
        os << LEAN_OBJ_TYPE << " ";
        mangle_name(os, c.m_name);
        os  << " = ";

        os << "lean::mk_obj(";
        os << c.m_ctor_index;
        os << ");" << std::endl;
    } else {
        os << LEAN_OBJ_TYPE << " ";
        mangle_name_fn_ptr(os, c.m_name);
        os  << "(";

        auto comma = false;

        std::vector<name> args;

        for (int i = 0; i < c.m_arity; i++) {
            std::string s = "f";
            s += ((char)(i + 48));
            auto arg = name(s.c_str());
            if (comma) {
                os << ", ";
            } else {
                comma = true;
            }
            os << LEAN_OBJ_TYPE << " ";
            mangle_name(os, arg);
            args.push_back(arg);
        }

        os << ") {" << std::endl;

        os << "return lean::mk_obj(";
        os << c.m_ctor_index;
        os << ", { ";

        comma = false;
        for (auto arg : args) {
            if (comma) {
                os << ", ";
            } else {
                comma = true;
            }
            mangle_name(os, arg);
        }
        os << " });";

        os << std::endl << "}" << std::endl;
    }
}

void clike_backend::generate_simple_expr(std::ostream& os, simple_expr const & se) {
    auto is_return = m_return;

    switch (se.kind()) {
        case simple_expr_kind::SVar:
            if (is_return) {
                os << "return ";
                generate_simple_expr_var(os, se);
                os << ";";
            } else {
                generate_simple_expr_var(os, se);
            }
            break;
        case simple_expr_kind::Call:
            if (is_return) {
                os << "return ";
                generate_simple_expr_call(os, se);
                os << ";";
            } else {
                generate_simple_expr_call(os, se);
            }
            break;
        case simple_expr_kind::Let:
            generate_simple_expr_let(os, se);
            break;
        case simple_expr_kind::Error:
            if (is_return) {
                os << "return ";
                generate_simple_expr_error(os, se);
                os << ";";
            } else {
                generate_simple_expr_error(os, se);
            }
            break;
        case simple_expr_kind::Switch:
            generate_simple_expr_switch(os, se);
            break;
        case simple_expr_kind::Project:
            generate_simple_expr_project(os, se);
            break;
        case simple_expr_kind::ClosureAlloc:
            generate_simple_expr_closure_alloc(os, se);
            break;
    }
}

}
