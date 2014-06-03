/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "util/lean_path.h"
#include "library/io_state_stream.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/parser_imp.h"
#include "frontends/lean/scanner.h"

namespace lean {
parser::parser(environment const & env, io_state const & ios, std::istream & in, char const * strm_name, script_state * S, bool use_exceptions, bool interactive) {
    parser_imp::show_prompt(interactive, ios);
    m_ptr.reset(new parser_imp(env, ios, in, strm_name, S, use_exceptions, interactive));
    m_ptr->m_this = m_ptr;
}

parser::~parser() {
}

bool parser::operator()() {
    return m_ptr->parse_commands();
}

expr parser::parse_expr() {
    return m_ptr->parse_expr_main();
}

io_state parser::get_io_state() const {
    return m_ptr->m_io_state;
}

bool parse_commands(environment const & env, io_state & ios, std::istream & in, char const * strm_name, script_state * S, bool use_exceptions, bool interactive) {
    parser p(env, ios, in, strm_name, S, use_exceptions, interactive);
    bool r = p();
    ios = p.get_io_state();
    return r;
}

bool parse_commands(environment const & env, io_state & ios, char const * fname, script_state * S, bool use_exceptions, bool interactive) {
    std::ifstream in(fname);
    if (in.bad() || in.fail())
        throw exception(sstream() << "failed to open file '" << fname << "'");
    return parse_commands(env, ios, in, fname, S, use_exceptions, interactive);
}

expr parse_expr(environment const & env, io_state & ios, std::istream & in, char const * strm_name, script_state * S, bool use_exceptions) {
    parser p(env, ios, in, strm_name, S, use_exceptions);
    expr r = p.parse_expr();
    ios = p.get_io_state();
    return r;
}

list<name> const & get_command_keywords();

void display_deps(std::ostream & out, char const * fname) {
    name import_name("import");
    std::ifstream in(fname);
    if (in.bad() || in.fail())
        throw exception(sstream() << "failed to open file '" << fname << "'");
    scanner s(in, fname);
    s.set_command_keywords(get_command_keywords());
    scanner::token t = s.scan();
    while (t != scanner::token::Eof) {
        if (t == scanner::token::CommandId && s.get_name_val() == import_name) {
            t = s.scan();
            while (t == scanner::token::Id) {
                std::string m_name = find_file(name_to_file(s.get_name_val()), {".olean", ".lua"});
                out << m_name << "\n";
                t = s.scan();
            }
        } else {
            t = s.scan();
        }
    }
}
}
