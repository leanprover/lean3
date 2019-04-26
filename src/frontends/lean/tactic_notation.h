/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parser.h"
namespace lean {
name get_interactive_tactic_full_name(name const & tac_class, name const & tac);
expr parse_begin_end_expr(parser & p, pos_info const & pos);
expr parse_curly_begin_end_expr(parser & p, pos_info const & pos);
expr parse_begin_end(parser & p, unsigned, expr const *, pos_info const & pos);
expr parse_by(parser & p, unsigned, expr const *, pos_info const & pos);
expr parse_interactive_tactic_block(parser & p, unsigned, expr const *, pos_info const & pos);
expr parse_nested_interactive_tactic(parser & p, name const & tac_class, bool use_istep);
void initialize_tactic_notation();
void finalize_tactic_notation();
}
