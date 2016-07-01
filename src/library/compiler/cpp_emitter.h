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
        void emit_indented(const char * str);
        void emit_string(const char * str);
        void emit_indented_line(const char * str);
        void mangle_name(name const & n);

        template <typename F>
        void emit_return(F expr) {
            this->emit_string("return ");
            expr();
            this->emit_string(";");
        }

        template <typename F>
        void emit_c_call(name const & global, unsigned nargs, expr const * args, F each_arg) {
            mangle_name(global);
            *this->m_output_stream << "(";

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
        void emit_local_call(unsigned bpz, unsigned nargs, expr const * args, F each_arg) {
            this->emit_local(bpz);
            *this->m_output_stream << "(";

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
        void emit_constructor(unsigned ctor, unsigned nargs, expr const * args, F each_arg) {
            *this->m_output_stream << "lean::mk_vm_constructor(";
            *this->m_output_stream << ctor << ", {";

            auto comma = false;

            for (unsigned i = 0; i < nargs; i++) {
                if (comma) {
                    *this->m_output_stream << ", ";
                } else {
                    comma = true;
                }
                each_arg(args[i]);
            }

            *this->m_output_stream << "})";
        }

        template <typename F>
        unsigned emit_local_binding(unsigned bpz, F value_fn) {
            *this->m_output_stream << LEAN_OBJ_TYPE << " ";
            this->emit_local(bpz);
            *this->m_output_stream << " = ";
            value_fn();
            *this->m_output_stream << ";" << std::endl;
            return bpz;
        }

        template <typename F>
        void emit_decl(name const & n, buffer<unsigned> & ls, expr e, F block_fn) {
            *this->m_output_stream << LEAN_OBJ_TYPE << " ";
            mangle_name(n);

            *this->m_output_stream << "(";

            auto comma = false;

            for (auto l : ls) {
                if (comma) {
                    *this->m_output_stream << ", ";
                } else {
                    comma = true;
                }
                *this->m_output_stream << LEAN_OBJ_TYPE << " ";
                this->emit_local(l);
            }

            *this->m_output_stream << ")";

            this->emit_block([e, block_fn] { block_fn(e); });
        }

        template <typename F>
        void emit_block(F block_fn) {
            *this->m_output_stream << "{\n";
            this->m_width += 4;
            block_fn();
            this->m_width -= 4;
            *this->m_output_stream << "}\n";
        }

        template <typename F>
        void emit_cases_on(name const & scrut, buffer<expr> & args, F action) {
            *this->m_output_stream << "cases_on " << args[0] << std::endl;
        }

        template <typename F>
        void emit_nat_cases(expr & scrutinee, expr & zero_case, expr & succ_case, F action) {
            this->emit_indented("vm::obj scrutinee = ");
            action(scrutinee);
            *this->m_output_stream << ";\n" << std::endl;

            this->emit_indented("if (is_simple(scrutinee))");
            this->emit_block([&] () {
                this->emit_indented("unsigned val = cidx(scrutinee);\n");
                this->emit_indented("if (val == 0) ");
                this->emit_block([&] () {
                    action(zero_case);
                    *this->m_output_stream << ";\n";
                });

                this->emit_indented("else ");

                this->emit_block([&] () {
                    action(succ_case);
                    *this->m_output_stream << ";\n";
                });
            });

            this->emit_indented("else ");
            this->emit_block([&] () {
                this->emit_indented("mpz const & val = to_mpz(top);\n");
                this->emit_indented("if (val == 0) ");
                this->emit_block([&] () {
                    action(zero_case);
                    *this->m_output_stream << ";\n";
                });

                this->emit_indented("else ");

                this->emit_block([&] () {
                    action(succ_case);
                });
            });
        }
    };
}
