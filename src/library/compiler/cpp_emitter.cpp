    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include "cpp_emitter.h"
#include "kernel/environment.h"

namespace lean {

void cpp_emitter::emit_headers() {
    *this->m_output_stream <<
        "#include <iostream>" << std::endl <<
        "#include \"util/numerics/mpz.h\"" << std::endl <<
        "#include \"library/vm/vm_io.h\"" << std::endl <<
        "#include \"library/vm/vm.h\"" << std::endl <<
        "#include \"init/init.h\"" << std::endl << std::endl;
}

void cpp_emitter::emit_unreachable() {
    *this->m_output_stream << "lean_unreachable()";
}

void cpp_emitter::emit_local(unsigned idx) {
    *this->m_output_stream << "_$local_" << idx;
}

void cpp_emitter::emit_sconstructor(unsigned idx) {
    *this->m_output_stream << "lean::mk_vm_simple(" << idx << ")";
}

void cpp_emitter::emit_mpz(mpz n) {
    *this->m_output_stream << "lean::mk_vm_mpz(lean::mpz(" << n << "))";
}

void cpp_emitter::emit_projection(unsigned idx) {
    *this->m_output_stream << "[" << idx << "]";
}

void cpp_emitter::indent() {
    this->m_width += 4;
}

void cpp_emitter::unindent() {
    this->m_width -= 4;
}

void cpp_emitter::mangle_name(name const & n) {
    if (n == name("main")) {
        *this->m_output_stream << "___lean__main";
    } else if (n.is_anonymous()) {
        *this->m_output_stream << "anon_name?";
    } else if (n.is_string()) {
        auto s = n.to_string("_");
        *this->m_output_stream << s;
    } else if (n.is_numeral()) {
        auto s = n.to_string("_");
        *this->m_output_stream << "__lean_nv_" << s;
    } else {
        lean_unreachable();
    }
}

void cpp_emitter::emit_prototype(name & n, unsigned arity) {
    *this->m_output_stream << "namespace lean {\n";
    *this->m_output_stream << "lean::vm_obj ";
    mangle_name(n);
    auto comma = false;

    *this->m_output_stream << "(";
    for (unsigned i = 0; i < arity; i++) {
        if (comma) {
            *this->m_output_stream << ", ";
        } else {
            comma = true;
        }
        *this->m_output_stream << "lean::vm_obj const &";
    }
    *this->m_output_stream << ");" << std::endl;
    *this->m_output_stream << "}\n";
}

void cpp_emitter::emit_string(const char * str) {
    *this->m_output_stream << str;
}

void cpp_emitter::emit_indented(const char * str) {
    this->m_output_stream->width(this->m_width);
    *this->m_output_stream << str;
    this->m_output_stream->width(0);
}

void cpp_emitter::emit_indented_line(const char * str) {
    this->m_output_stream->width(this->m_width);
    *this->m_output_stream << str << std::endl;
    this->m_output_stream->width(this->m_width);
}

void cpp_emitter::emit_main(name & lean_main) {
    *this->m_output_stream << "int main() {\n";
        // "lean::initialize();\n" <<
        // "lean::environment env;\n";
    mangle_name(lean_main);
    *this->m_output_stream << "();\n" << "return 0;\n}" << std::endl;
}
}
