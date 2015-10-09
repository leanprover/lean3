/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Rob Lewis
*/
#include "library/norm_num.h"
namespace lean {
static name * g_one     = nullptr;
static name * g_zero    = nullptr;
static name * g_bitone  = nullptr;
static name * g_bitzero = nullptr;

static bool is_numeral_aux(expr const & e, bool is_first) {
    // TODO(Rob)
   // std::cout << ">>>>> where does this go\n";
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    if (!is_constant(f)) {
      std::cout << ">>>> not constant";
      return false;
    }
    if (const_name(f) == *g_one) {
        //std::cout << ">>>> g_one";
        return args.size() == 2;
    } else if (const_name(f) == *g_zero) {
        //std::cout << ">>>> g_zero";
        return is_first && args.size() == 2;
    } else if (const_name(f) == *g_bitone) {
        //std::cout << ">>>> bit: size of args " << std::to_string(args.size());
        return args.size() == 4 && is_numeral_aux(args[3], false);
    } else if (const_name(f) == *g_bitzero) {
        return args.size() == 3 && is_numeral_aux(args[2], false);
    }
    return false;
}

bool norm_num_context::is_numeral(expr const & e) const {
    return is_numeral_aux(e, true);
}

pair<expr, expr> norm_num_context::mk_norm(expr const & e) {
    // TODO(Rob)
    std::cout << "HERE1\n";
    if (!is_numeral(e)) {
        throw exception("norm_num applied to non numeral");
    }
    // detect how numeral is assembled, find appropriate lemma below
    throw exception("not implemented yet - norm_num");
}

pair<expr, expr> norm_num_context::mk_norm_add(expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet -- mk_norm_add");
}

pair<expr, expr> norm_num_context::mk_norm_mul(expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet -- mk_norm_mul");
}

pair<expr, expr> norm_num_context::mk_norm_div(expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet -- mk_norm_div");
}

pair<expr, expr> norm_num_context::mk_norm_sub(expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet -- mk_norm_sub");
}

void initialize_norm_num() {
  g_one     = new name("one");
  g_zero    = new name("zero");
  g_bitone  = new name("bit1");
  g_bitzero = new name("bit0");
}

void finalize_norm_num() {
  delete g_one;
  delete g_zero;
  delete g_bitone;
  delete g_bitzero;
}
}
