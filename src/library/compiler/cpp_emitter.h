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
        void emit_mk_nat(mpz n);
        void emit_sconstructor(unsigned idx);
        void emit_projection(unsigned idx);
        void indent();
        void unindent();

        void emit_main(name & lean_main) {
            emit_main(lean_main, [&] () {});
        }

        template<typename F>
        void emit_main(name & lean_main, F f) {
            *this->m_output_stream << "int main() {\n";
            this->emit_indented_line("lean::initialize();");
            this->emit_indented_line("lean::environment env;");
            f();
            this->emit_indented_line("lean::vm_state S(env);");
            this->emit_indented_line("lean::scope_vm_state scoped(S);");
            this->emit_indented_line("g_env = &env;");
            mangle_name(lean_main);
            *this->m_output_stream << "();\n" << "return 0;\n}" << std::endl;
        }
        void emit_prototype(name const & n, unsigned arity);
        void emit_indented(const char * str);
        void emit_string(const char * str);
        void emit_indented_line(const char * str);
        void mangle_name(name const & n);
        void emit_declare_vm_builtin(name const & n);

        template <typename F>
        void emit_return(F expr) {
            this->emit_indented("return ");
            expr();
            this->emit_string(";\n");
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
        void emit_mk_native_closure(name const & global, unsigned nargs, expr const * args, F each_arg) {
            this->emit_string("lean::mk_native_closure(*g_env, lean::name({\"");
            *this->m_output_stream << global.to_string("\"}, {\"");
            this->emit_string("\"}), ");

            *this->m_output_stream << "{";

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
        void emit_local_call(unsigned bpz, unsigned nargs, expr const * args, F each_arg) {
            *this->m_output_stream << "lean::invoke(";
            this->emit_local(bpz);

            for (unsigned i = 0; i < nargs; i++) {
                *this->m_output_stream << ", ";
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
                *this->m_output_stream << LEAN_OBJ_TYPE << " const & ";
                this->emit_local(l);
            }

            *this->m_output_stream << ")";

            this->emit_block([e, block_fn] { block_fn(e); });

            *this->m_output_stream << "\n";
        }

        template <typename F>
        void emit_block(F block_fn) {
            *this->m_output_stream << "{\n";
            this->indent();
            block_fn();
            this->unindent();
            emit_indented_line("}");
        }

        template <typename F>
        void emit_cases_on(name const & scrut, buffer<expr> & args, F action) {
            this->emit_indented("switch (cidx(");
            action(args[0]);
            this->emit_string("))");
            this->emit_block([&] () {
                for (unsigned i = 1; i < args.size(); i++) {
                    this->emit_indented("case ");
                    *this->m_output_stream << i - 1;
                    this->emit_string(":");
                    this->emit_block([&] () {
                        action(args[i]);
                        this->emit_indented("break;\n");
                    });
                }

                this->emit_indented("default:\n");
                this->emit_indented("throw std::runtime_error(");
                this->emit_string("\"code-gen error\"");
                this->emit_string(");\n");
            });
        }

        template <typename F>
        void emit_builtin_cases_on(name const & cases_on, buffer<expr> & args, F action) {
            // this->emit_indented("auto idx = get_vm_builtin_cases_idx(name({");
            // *this->m_output_stream << name << "}))"
            // this->emit_indented("switch (get_vm_builtin_cases_idx(name({");
            // *this->m_output_stream << name << "}))"
            // this->emit_string("))");
            // this->emit_block([&] () {
            //     for (unsigned i = 1; i < args.size(); i++) {
            //         this->emit_indented("case ");
            //         *this->m_output_stream << i - 1;
            //         this->emit_string(":");
            //         this->emit_block([&] () {
            //             action(args[i]);
            //             this->emit_indented("break;\n");
            //         });
            //     }
            //
            //     this->emit_indented("default:\n");
            //     this->emit_indented("throw std::runtime_error(");
            //     this->emit_string("\"code-gen error\"");
            //     this->emit_string(");\n");
            // });
        }

        template <typename F>
        void emit_nat_cases(expr const & scrutinee, expr const & zero_case, expr const & succ_case, F action) {

            this->emit_indented("if (is_simple(");
            action(scrutinee);
            this->emit_string("))");
            this->emit_block([&] () {
                this->emit_indented("if (cidx(");
                action(scrutinee);
                this->emit_string(") == 0) ");
                this->emit_block([&] () {
                    action(zero_case);
                    *this->m_output_stream << ";\n";
                });

                this->emit_string("else ");

                this->emit_block([&] () {
                    action(succ_case);
                    *this->m_output_stream << ";\n";
                });
            });

            this->emit_string("else ");
            this->emit_block([&] () {
                this->emit_indented("if (to_mpz(");
                action(scrutinee);
                this->emit_string(") == 0) ");
                this->emit_block([&] () {
                    action(zero_case);
                    *this->m_output_stream << ";\n";
                });

                this->emit_string("else ");

                this->emit_block([&] () {
                    action(succ_case);
                });
            });
        }
    };
}
