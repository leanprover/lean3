    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include "rust_backend.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/instantiate.h"
#include "used_names.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {

static const char * LEAN_RUST_OBJ_TYPE = "lean::Object";
static const char * LEAN_RUST_ERR = "lean::runtime_error";
static const char * LEAN_RUST_FN_PTR_SUFFIX = "_fn_ptr";
static const char * LEAN_RUST_MAIN = "___LEAN_RUST__main";
static const char * LEAN_RUST_FRESH_N_PREFIX = "__$lean$_$";

rust_backend::rust_backend(environment const & env, config & conf)
    : clike_backend(env, conf), m_return(false) {}

void rust_backend::generate_includes(std::ostream& os) {
    os << "extern crate lean_rts as lean;" << std::endl << std::endl;
}

void rust_backend::generate_main(std::ostream& os, std::string main_fn) {
    os << "fn main() {" << std::endl;
    os << std::setw(4) << "lean::run_main(";
    mangle_name(os, main_fn);
    os << LEAN_RUST_FN_PTR_SUFFIX;
    os << ");" << std::endl;
    os << "}" << std::endl;
}

void rust_backend::generate_ctor(std::ostream& os, ctor const & c) {
    if (c.m_arity == 0) {
        os << "static ";
        os << LEAN_RUST_OBJ_TYPE << " ";
        mangle_name(os, c.m_name);
        os  << " = ";

        os << "lean::mk_obj(";
        os << c.m_ctor_index;
        os << ");" << std::endl;
    } else {
        os << LEAN_RUST_OBJ_TYPE << " ";
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
            os << LEAN_RUST_OBJ_TYPE << " ";
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

void rust_backend::generate_proc(std::ostream& os, proc const & p) {
    os << "fn ";
    mangle_name_fn_ptr(os, p.m_name);
    os << "(";

    auto comma = false;

    for (auto arg : p.m_args) {
        if (comma) {
            os << ", ";
        } else {
            comma = true;
        }
        mangle_name(os, arg);
        os << ": " << LEAN_RUST_OBJ_TYPE;
    }

    os << ") {" << std::endl;
    os << std::left << std::setw(4);
    os.flush();

    if (this->m_debug_tracing) {
        os << "std::cout << " << "\"";
        mangle_name_fn_ptr(os, p.m_name);
        os << "\"" << " << std::endl;\n";
    }

    m_return = true;
    this->generate_simple_expr(os, *p.m_body);

    os << std::endl << "}" << std::endl;
}

void rust_backend::generate_decl(std::ostream& os, proc const & p) {
    os << "static ";
    os << LEAN_RUST_OBJ_TYPE << " ";
    mangle_name(os, p.m_name);
    os << " = ";
    os << "mk_closure(";
    mangle_name_fn_ptr(os, p.m_name);
    os << ", ";
    os << p.arity();
    os << ", 0, nullptr);";
    os << "\n";
}

void rust_backend::generate_simple_expr_var(std::ostream& os, simple_expr const & se) {
    auto n = to_simple_var(&se)->m_name;
    mangle_name(os, n);
}

void rust_backend::generate_simple_expr_error(std::ostream& os, simple_expr const & se) {
    auto msg = to_simple_error(&se)->m_error_msg;
    os << LEAN_RUST_ERR << "(\"" << msg.c_str() << "\")";
}

void rust_backend::generate_simple_expr_call(std::ostream& os, simple_expr const & se) {
    auto args = to_simple_call(&se)->m_args;
    auto callee = to_simple_call(&se)->m_name;
    auto direct = to_simple_call(&se)->m_direct;

    auto opt_proc = this->m_procs.contains(callee);
    // Here we need to decide how we to call the callee
    // there are 3-cases with our code generation strategy.
    //
    // The first case is we generated a zero arity fn_ptr
    // and we must directly call it to produce the value.
    //
    // The next is a call marked a direct, with a non-zero
    // arity meaning we can directly apply it to all of its
    // arguments.
    //
    // Final case is a non-zero arity, in-direct call which
    // must be called via the `apply` method.
    if (opt_proc && this->m_procs.find(callee)->m_arity == 0) {
        mangle_name_fn_ptr(os, callee);
        os << "().apply(";
    } else {
        if (!direct) {
            mangle_name(os, callee);
            os << ".apply(";
        } else {
            mangle_name_fn_ptr(os, callee);
            os << "(";
        }
    }

    // No matter which case we pick above we uniformly emit arguments.
    auto comma = false;

    int i = 0;
    for (auto name : args) {
        if (comma) {
            os << ", ";
        } else {
            comma = true;
        }
        mangle_name(os, name);
        i += 1;
    }

    os << ")";
}

void rust_backend::generate_binding(std::ostream& os, pair<name, shared_ptr<simple_expr>> & p) {
    auto n = p.first;
    auto se = p.second;

    os << "let" << " ";
    mangle_name(os, n);
    os << " = ";
    this->generate_simple_expr(os, *se);
    os << ";" << std::endl;
}

void rust_backend::generate_simple_expr_let(std::ostream& os, simple_expr const & se) {
    auto should_return = m_return;

    auto bindings = to_simple_let(&se)->m_bindings;
    auto body = to_simple_let(&se)->m_body;

    for (auto binding : bindings) {
        // We shouldn't return out of any rhs of a let binding.
        m_return = false;
        this->generate_binding(os, binding);
    }

    m_return = should_return;
    this->generate_simple_expr(os, *body);
}

void rust_backend::generate_simple_expr_switch(std::ostream& os, simple_expr const & se) {
    auto scrutinee = to_simple_switch(&se)->m_scrutinee;
    auto cases = to_simple_switch(&se)->m_cases;
    os << "match ";
    mangle_name(os, scrutinee);
    os << ".ctor_id() {" << std::endl;
    int i = 0;
    for (auto c : cases) {
        os << i << " => {\n" << std::endl;
        generate_simple_expr(os, *c);
        os << "}\n";
        i += 1;
    }
    os << "_ => {\n";
    os << LEAN_RUST_ERR << "(\"" << "recursor-compilation-failure" << "\")" << std::endl;
    os << "}}\n";
}

void rust_backend::generate_simple_expr_project(std::ostream& os, simple_expr const & se) {
    auto projection = to_simple_project(&se);
    mangle_name(os, projection->m_name);
    os << "[";
    os << projection->m_index;
    os << "]";
}

void rust_backend::generate_simple_expr_closure_alloc(std::ostream& os, simple_expr const & se) {
    auto closure_alloc = to_simple_closure_alloc(&se);
    os << "lean::mk_closure(";
    mangle_name_fn_ptr(os, closure_alloc->m_name);
    os << ",";
    os << closure_alloc->m_arity;
    os << ",";
    os << "{";
    auto comma = false;
    for (auto fv : closure_alloc->m_free_vars) {
        if (comma) {
            os << ",";
            mangle_name(os, fv);
        } else {
            comma = true;
            mangle_name(os, fv);
        }
    }
    os << "}";
    os << ")";
}

}
