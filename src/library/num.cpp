/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/num.h"
#include "library/util.h"
#include "library/constants.h"

namespace lean {
bool has_num_decls(environment const & env) {
    return
        env.find(get_zero_name()) &&
        env.find(get_one_name()) &&
        env.find(get_bit0_name()) &&
        env.find(get_bit1_name());
}

optional<expr> unfold_num_app(environment const & env, expr const & e) {
    if (is_zero(e) || is_one(e) || is_bit0(e) || is_bit1(e)) {
        return unfold_app(env, e);
    } else {
        return none_expr();
    }
}

bool is_numeral_const_name(name const & n) {
    return n == get_zero_name() || n == get_one_name() || n == get_bit0_name() || n == get_bit1_name();
}

static bool is_num(expr const & e, bool first) {
    expr arg;
    if (is_zero(e))
        return first;
    else if (is_one(e))
        return true;
    else if (is_bit0(e, arg))
        return is_num(arg, false);
    else if (is_bit1(e, arg))
        return is_num(arg, false);
    else
        return false;
}

bool is_num(expr const & e) {
    return is_num(e, true);
}

static optional<mpz> to_num(expr const & e, bool first) {
    expr arg;
    if (is_zero(e)) {
        return first ? some(mpz(0)) : optional<mpz>();
    } else if (is_one(e)) {
        return some(mpz(1));
    } else if (is_bit0(e, arg)) {
        if (auto r = to_num(arg, false))
            return some(2*(*r));
    } else if (is_bit1(e, arg)) {
        if (auto r = to_num(arg, false))
            return some(2*(*r)+1);
    } else if (is_neg(e, arg)) {
        if (auto r = to_num(arg, false))
            return some(neg(*r));
    }
    return optional<mpz>();
}

optional<mpz> to_num(expr const & e) {
    return to_num(e, true);
}

optional<mpz> to_pos_num(expr const & e) {
    if (is_constant(e, get_pos_num_one_name())) {
         return some(mpz(1));
    } else if (is_const_app(e, get_pos_num_bit0_name(), 1)) {
        if (auto r = to_pos_num(app_arg(e)))
            return some(2*(*r));
    } else if (is_const_app(e, get_pos_num_bit1_name(), 1)) {
        if (auto r = to_pos_num(app_arg(e)))
            return some(2*(*r) + 1);
    }
    return optional<mpz>();
}

optional<mpz> to_num_core(expr const & e) {
    if (is_constant(e, get_num_zero_name()))
        return some(mpz(0));
    else if (is_const_app(e, get_num_pos_name(), 1))
        return to_pos_num(app_arg(e));
    else
        return optional<mpz>();
}

bool is_num_leaf_constant(name const & n) {
    return
        n == get_zero_name() ||
        n == get_one_name() ||
        n == get_has_zero_zero_name() ||
        n == get_has_one_one_name();
}
}
