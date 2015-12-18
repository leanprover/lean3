/*
  Copyright (c) 2015 Daniel Selsam. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Daniel Selsam
*/
#include "library/blast/arith/num.h"
#include "library/constants.h"
#include "library/blast/simplifier/simplifier.h"
#include "library/blast/arith/simplify.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {

using simp::result;

/* Helpers */
static bool is_numeral_head(name const & n) {
    return n == get_one_name() || n == get_zero_name() || n == get_bit0_name() || n == get_bit1_name();
}

static bool is_arithmetic(name const & n) {
    // TODO(dhs): what about power? probably all sorts of other things too
    return n == get_add_name() || n == get_mul_name() || n == get_neg_name() || n == get_inv_name();
}

/* Simplify without proof */

class simplify_fn {
    static void simplify_add_core(expr const & e, polynomial & p, bool inv, bool neg) {
        expr e1, e2;
        if (is_add(e, e1, e2)) {
            simplify_add_core(e1, p, inv, neg);
            simplify_add_core(e2, p, inv, neg);
        } else {
            p.add(simplify(e, inv, neg));
        }
    }

    static polynomial simplify_add(expr const & e, bool inv, bool neg) {
        lean_assert(is_add(e));
        if (inv) {
            return polynomial(e, inv, neg);
        } else {
            polynomial p;
            simplify_add_core(e, p, inv, neg);
            return p;
        }
    }

    static void simplify_mul_core(expr const & e, polynomial & p, bool inv, bool neg) {
        expr e1, e2;
        if (is_mul(e, e1, e2)) {
            simplify_mul_core(e1, p, inv, neg);
            simplify_mul_core(e2, p, inv, neg);
        } else {
            p.mul(simplify(e, inv, neg));
        }
    }

    static polynomial simplify_mul(expr const & e, bool inv, bool neg) {
        lean_assert(is_mul(e));
        polynomial p(mpq(1), inv, neg);
        simplify_mul_core(e, p, inv, false);
        return p;
    }

    static polynomial simplify(expr const & e, bool inv, bool neg) {
        expr f = get_app_fn(e);
        if (!is_constant(f)) {
            return polynomial(e, inv, neg);
        } else if (is_numeral_head(const_name(f))) {
            return polynomial(expr_to_mpq(e), inv, neg);
        } else if (!is_arithmetic(const_name(f))) {
            return polynomial(e, inv, neg);
        } else if (const_name(f) == get_add_name()) {
            return simplify_add(e, inv, neg);
        } else if (const_name(f) == get_mul_name()) {
            return simplify_mul(e, inv, neg);
        } else if (const_name(f) == get_neg_name()) {
            return simplify(app_arg(e), inv, !neg);
        } else if (const_name(f) == get_inv_name()) {
            return simplify(app_arg(e), !inv, neg);
        } else {
            throw exception("TODO(dhs): some case not handled");
        }
    }
public:
    polynomial operator()(expr const & e) { return simplify(e, false, false); }
};

/* Simplify with proof */
class simplify_with_proof_fn {
    result simplify_add(expr const &, expr const &) {
        throw exception("TODO(dhs): simplify_add");
    }

    result simplify_mul(expr const &, expr const &) {
        throw exception("TODO(dhs): simplify_mul");
    }
    result simplify_neg(expr const &) {
        throw exception("TODO(dhs): simplify_neg");
    }
    result simplify_inv(expr const &) {
        throw exception("TODO(dhs): simplify_inv");
    }

    result simplify(expr const & e) {
        expr arg, arg1, arg2;
        if (is_numeral_expr(e)) {
            return normalize_numeral_expr(e);
        } else if (is_add(e, arg1, arg2)) {
            return simplify_add(arg1, arg2);
        } else if (is_mul(e, arg1, arg2)) {
            return simplify_mul(arg1, arg2);
        } else if (is_neg(e, arg)) {
            return simplify_neg(arg);
        } else if (is_inv(e, arg)) {
            return simplify_inv(arg);
        } else {
            return result(e);
        }
    }
public:
    result operator()(expr const & e) { return simplify(e); }
};

/* Entry points */
polynomial arith::simplify(expr const & e) {
    polynomial p = simplify_fn()(e);
    p.fuse_monomials();
    return p;
}

result arith::simplify_with_proof(expr const & e) {
    return simplify_with_proof_fn()(e);
}

}}
