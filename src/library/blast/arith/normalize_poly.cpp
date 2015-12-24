/*
  Copyright (c) 2015 Daniel Selsam. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Daniel Selsam
*/
#include "library/blast/arith/num.h"
#include "library/constants.h"
#include "library/blast/arith/normalize_poly.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {

/* Helpers */
static bool is_numeral_head(name const & n) {
    return n == get_one_name() || n == get_zero_name() || n == get_bit0_name() || n == get_bit1_name();
}

static bool is_arithmetic(name const & n) {
    // TODO(dhs): what about power? probably all sorts of other things too
    return n == get_add_name() || n == get_mul_name() || n == get_neg_name() || n == get_inv_name();
}

/* Normalize without proof */

class normalize_poly_fn {
    static void normalize_add_core(expr const & e, polynomial & p, bool inv, bool neg) {
        expr e1, e2;
        if (is_add(e, e1, e2)) {
            normalize_add_core(e1, p, inv, neg);
            normalize_add_core(e2, p, inv, neg);
        } else {
            p.add(normalize(e, inv, neg));
        }
    }

    static polynomial normalize_add(expr const & e, bool inv, bool neg) {
        lean_assert(is_add(e));
        if (inv) {
            return polynomial(e, inv, neg);
        } else {
            polynomial p;
            normalize_add_core(e, p, inv, neg);
            return p;
        }
    }

    static void normalize_mul_core(expr const & e, polynomial & p, bool inv, bool neg) {
        expr e1, e2;
        if (is_mul(e, e1, e2)) {
            normalize_mul_core(e1, p, inv, neg);
            normalize_mul_core(e2, p, inv, neg);
        } else {
            p.mul(normalize(e, inv, neg));
        }
    }

    static polynomial normalize_mul(expr const & e, bool inv, bool neg) {
        lean_assert(is_mul(e));
        polynomial p(mpq(1), inv, neg);
        normalize_mul_core(e, p, inv, false);
        return p;
    }

    static polynomial normalize(expr const & e, bool inv, bool neg) {
        expr f = get_app_fn(e);
        if (!is_constant(f)) {
            return polynomial(e, inv, neg);
        } else if (is_numeral_head(const_name(f))) {
            return polynomial(expr_to_mpq(e), inv, neg);
        } else if (!is_arithmetic(const_name(f))) {
            return polynomial(e, inv, neg);
        } else if (const_name(f) == get_add_name()) {
            return normalize_add(e, inv, neg);
        } else if (const_name(f) == get_mul_name()) {
            return normalize_mul(e, inv, neg);
        } else if (const_name(f) == get_neg_name()) {
            return normalize(app_arg(e), inv, !neg);
        } else if (const_name(f) == get_inv_name()) {
            return normalize(app_arg(e), !inv, neg);
        } else {
            throw exception("TODO(dhs): some case not handled");
        }
    }
public:
    polynomial operator()(expr const & e) { return normalize(e, false, false); }
};

/* Entry point */
polynomial arith::normalize_poly(expr const & e) {
    polynomial p = normalize_poly_fn()(e);
    p.fuse_monomials();
    return p;
}
}}
