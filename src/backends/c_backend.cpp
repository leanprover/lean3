    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include "c_backend.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/instantiate.h"
#include "used_names.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {

static const char * LEAN_OBJ_TYPE = "lean::obj";

c_backend::c_backend(environment const & env, optional<std::string> main_fn)
    : backend(env, main_fn), m_return(false) {}

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

void generate_includes(std::ostream& os) {
    os << "#include \"lean_runtime.h\"" << std::endl << std::endl;
    os << "#include \"string.h\"" << std::endl << std::endl;
}

void generate_main(std::ostream& os, std::string main_fn) {
    os << "int main() {" << std::endl;
    os << std::setw(4) << "lean::run_lean_main(";
    mangle_name(os, main_fn);
    os << LEAN_FN_PTR_SUFFIX;
    os << ");" << std::endl;
    os << std::setw(4) << "return 0;" << std::endl;
    os << "}" << std::endl;
}

void c_backend::generate_code(optional<std::string> output_path) {
    // auto fs_ptr = m_emitter.m_output_stream.get();
    //std::ostream & fs = reinterpret_cast<std::ostream &>(fs_ptr);
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
    generate_main(fs, "main");
    fs.flush();
}

void c_backend::generate_ctor(std::ostream& os, ctor const & c) {
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

void c_backend::generate_proc(std::ostream& os, proc const & p) {
    os << LEAN_OBJ_TYPE << " ";
    mangle_name_fn_ptr(os, p.m_name);
    os << "(";

    auto comma = false;

    for (auto arg : p.m_args) {
        if (comma) {
            os << ", ";
        } else {
            comma = true;
        }
        os << LEAN_OBJ_TYPE << " ";
        mangle_name(os, arg);
    }

    os << ") {" << std::endl;
    os << std::left << std::setw(4);
    os.flush();

    os << "std::cout << " << "\"";
    mangle_name_fn_ptr(os, p.m_name);
    os << "\"" << " << std::endl;\n";

    m_return = true;
    this->generate_simple_expr(os, *p.m_body);

    os << std::endl << "}" << std::endl;
}

void c_backend::generate_decl(std::ostream& os, proc const & p) {
    os << LEAN_OBJ_TYPE << " ";
    mangle_name_fn_ptr(os, p.m_name);
    os << "(";

    auto comma = false;

    for (auto arg : p.m_args) {
        if (comma) {
            os << ", ";
        } else {
            comma = true;
        }
        os << LEAN_OBJ_TYPE << " ";
        mangle_name(os, arg);
    }

    os << ");" << std::endl;

    os << "static ";
    os << LEAN_OBJ_TYPE << " ";
    mangle_name(os, p.m_name);
    os << " = ";
    os << "mk_closure(";
    mangle_name_fn_ptr(os, p.m_name);
    os << ", ";
    os << p.arity();
    os << ", 0, nullptr);";
    os << "\n";
}

void c_backend::generate_simple_expr_var(std::ostream& os, simple_expr const & se) {
    auto n = to_simple_var(&se)->m_name;
    mangle_name(os, n);
}

void c_backend::generate_simple_expr_error(std::ostream& os, simple_expr const & se) {
    auto msg = to_simple_error(&se)->m_error_msg;
    os << "error(\"" << msg.c_str() << "\")";
}

void c_backend::generate_simple_expr_call(std::ostream& os, simple_expr const & se) {
    auto args = to_simple_call(&se)->m_args;
    auto callee = to_simple_call(&se)->m_name;
    auto direct = to_simple_call(&se)->m_direct;

    if (args.size() == 0) {
        mangle_name(os, callee);
        return;
    }

    if (!direct) {
        mangle_name(os, callee);
        os << ".apply(";
    } else {
        mangle_name_fn_ptr(os, callee);
        os << "(";
    }

    auto comma = false;

    for (auto name : args) {
        if (comma) {
            os << ", ";
        } else {
            comma = true;
        }
        mangle_name(os, name);
    }

    os << ")";
}

void c_backend::generate_binding(std::ostream& os, pair<name, shared_ptr<simple_expr>> & p) {
    auto n = p.first;
    auto se = p.second;

    os << LEAN_OBJ_TYPE << " ";
    mangle_name(os, n);
    os << " = ";
    this->generate_simple_expr(os, *se);
    os << ";" << std::endl;
}

void c_backend::generate_simple_expr_let(std::ostream& os, simple_expr const & se) {
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

void c_backend::generate_simple_expr_switch(std::ostream& os, simple_expr const & se) {
    auto scrutinee = to_simple_switch(&se)->m_scrutinee;
    auto cases = to_simple_switch(&se)->m_cases;
    os << "switch (";
    mangle_name(os, scrutinee);
    os << ".cidx()) {" << std::endl;
    int i = 0;
    for (auto c : cases) {
        os << "case " << i << ": {\n" << std::endl;
        generate_simple_expr(os, *c);
        os << "}\n";
    }
    os << "default:\n";
    os << "return " << LEAN_ERR << "(\"" << "recursor-compilation-failure" << "\");" << std::endl;
    os << "}\n";
}

void c_backend::generate_simple_expr_project(std::ostream& os, simple_expr const & se) {
    auto projection = to_simple_project(&se);
    mangle_name(os, projection->m_name);
    os << "[";
    os << projection->m_index;
    os << "]";
}

void c_backend::generate_simple_expr_closure_alloc(std::ostream& os, simple_expr const & se) {
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

void c_backend::generate_simple_expr(std::ostream& os, simple_expr const & se) {
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
