/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "kernel/environment.h"
#include "kernel/expr.h"

namespace lean  {
    static const char * LEAN_OBJ_TYPE = "lean::vm_obj";
    // static const char * LEAN_ERR = "lean::runtime_error";

    class cpp_emitter {
        int m_width;
    public:
        std::fstream * m_output_stream;

        cpp_emitter(std::string path) : m_output_stream(nullptr), m_width(0) {
            this->m_output_stream =
                new std::fstream(path.c_str(), std::ios_base::out);
        }

        ~cpp_emitter() {
            this->m_output_stream->flush();
            this->m_output_stream->close();
            delete this->m_output_stream;
        }

        void emit_headers();
        void emit_unreachable();
        void emit_local(unsigned idx);
        void emit_mpz(mpz n);
        void emit_sconstructor(unsigned idx);
        void emit_projection(unsigned idx);
        void indent();
        void unindent();
        void emit_main(name & lean_main);
        void emit_prototype(name & n, unsigned arity);

        void mangle_name(name const & n);

        template <typename F>
        void emit_return(F expr) {
            *this->m_output_stream << "return ";
            expr();
            *this->m_output_stream << ";\n";
        }

        template <typename F>
        void emit_c_call(name & global, unsigned nargs, expr const * args, F each_arg) {
            *this->m_output_stream << global << "(";

            auto comma = false;

            for (unsigned i = 0; i < nargs; i++) {
                if (comma) {
                    *this->m_output_stream << ", ";
                } else {
                    comma = true;
                }
                each_arg(args[i]);
            }

            *this->m_output_stream << ")";
        }

        template <typename F>
        void emit_local_binding(unsigned bpz, F value_fn) {
            *this->m_output_stream << LEAN_OBJ_TYPE << " ";
            this->emit_local(bpz);
            *this->m_output_stream << " = ";
            value_fn();
            *this->m_output_stream << ";" << std::endl;
        }

        template <typename F>
        void emit_decl(name const & n, expr e, F block_fn) {
            *this->m_output_stream << LEAN_OBJ_TYPE << " ";
            mangle_name(n);
            *this->m_output_stream << "() ";
            this->emit_block([e, block_fn] { block_fn(e); });
        }

        template <typename F>
        void emit_block(F block_fn) {
            *this->m_output_stream << "{" << std::endl;
            this->m_width += 4;
            block_fn();
            this->m_width -= 4;
            *this->m_output_stream << "}" << std::endl;
        }

        // void emit_return(expr const & e)
    };
}
