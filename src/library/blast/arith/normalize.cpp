/*
  Copyright (c) 2015 Daniel Selsam. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Daniel Selsam
*/
#include "library/blast/arith/num.h"
#include "library/constants.h"
#include "util/sexpr/option_declarations.h"
#include "library/blast/trace.h"
#include "library/blast/blast.h"
#include "kernel/type_checker.h"
#include "kernel/expr.h"
#include "library/blast/blast_exception.h"
#include "library/blast/arith/normalize.h"

#ifndef LEAN_DEFAULT_ARITH_NORMALIZE_MAX_STEPS
#define LEAN_DEFAULT_ARITH_NORMALIZE_MAX_STEPS 500
#endif

namespace lean {
namespace blast {

/* TODO(dhs): For performance,
   1. Track reflexivity like we do in the simplifier.
   2. Cache.
*/

using simp::result;

/* Globals */
static name * g_normalize_trace_name       = nullptr;
static name * g_normalize_error_trace_name = nullptr;
static name * g_arith_normalize_max_steps  = nullptr;

unsigned get_arith_normalize_max_steps() {
    return ios().get_options().get_unsigned(*g_arith_normalize_max_steps, LEAN_DEFAULT_ARITH_NORMALIZE_MAX_STEPS);
}

/* Normalize with proof */
class normalize_fn {
    unsigned m_num_steps{0};
    unsigned m_max_steps{get_arith_normalize_max_steps()};

    expr m_type;
    expr m_zero;
    expr m_one;
    expr m_negative_one;

    /* We create locals for non-zero proofs */
    expr_struct_map<expr> m_placeholders;

    expr prove_nonzero(expr const & e) {
        auto it = m_placeholders.find(e);
        if (it != m_placeholders.end()) {
            return it->second;
        } else {
            expr thm = get_app_builder().mk_not(get_app_builder().mk_eq(e, m_zero));
            expr pf = mk_fresh_local(thm);
            m_placeholders.insert({e, pf});
            return pf;
        }
    }


    bool is_lt(expr const & e1, expr const & e2) {
        /* The order is crucial for our simple fusion algorithm to work.
           1. Numerals are the least (and none are less than each other)
           2. Then we make left-multiplication by a numeral a "light" wrapper
           3. Then we use the "light"-less-than from the environment, which
              we assume has `neg` and `inv` set to be light at the right arguments.
        */
        expr arg1, arg2;
        if (is_normalized_numeral(e2)) {
            return false;
        } else if (is_normalized_numeral(e1)) {
            return true;
        } else if (is_mul(e1, arg1, arg2) && is_normalized_numeral(arg1)) {
            return is_lt(arg2, e2);
        } else if (is_mul(e2, arg1, arg2) && is_normalized_numeral(arg1)) {
            return !is_lt(arg2, e1);
        } else {
            return is_light_lt(e1, e2);
        }
    }

    expr_pair join(unsigned nargs, expr_pair const * args) {
        expr_pair r = args[0];
        for (unsigned i = 1; i < nargs; ++i) {
            r = mk_pair(args[i].first, get_app_builder().mk_eq_trans(r.second, args[i].second));
        }
        return r;
    }

    expr_pair join(std::initializer_list<expr_pair> const & args) {
        return join(args.size(), args.begin());
    }

    expr_pair refl(expr const & e) { return mk_pair(e, get_app_builder().mk_eq_refl(e)); }

    expr_pair finalize(result const & r) {
        if (r.has_proof()) return mk_pair(r.get_new(), r.get_proof());
        else return mk_pair(r.get_new(), get_app_builder().mk_eq_refl(r.get_new()));
    }

    expr_pair normalize_numeral_expr(expr const & e) {
        return finalize(::lean::blast::normalize_numeral_expr(e));
    }

    expr_pair add_insert_flat(expr const & e, expr const & flat_rhs) {
        expr arg1, arg2;
        expr arg2_1, arg2_2;
        if (!is_add(e, arg1, arg2)) {
            return refl(get_app_builder().mk_add(m_type, e, flat_rhs));
        } else if (!is_add(arg1) && !is_add(arg2)) {
            return mk_pair(get_app_builder().mk_add(m_type, arg1,
                                                    get_app_builder().mk_add(m_type, arg2, flat_rhs)),
                           get_app_builder().mk_app(get_add_assoc_name(), {arg1, arg2, flat_rhs}));
        } else {
            // lemma add_insert_flat [s : add_semigroup A] : b + c = y → a + y = z → (a + b) + c = z
            expr_pair r1 = add_insert_flat(arg2, flat_rhs);
            expr_pair r2 = add_insert_flat(arg1, r1.first);
            return mk_pair(r2.first, get_app_builder().mk_app(get_blast_arith_add_insert_flat_name(), {r1.second, r2.second}));
        }
    }

    expr_pair add_flatten(expr const & e) {
        expr arg1, arg2;
        if (is_add(e, arg1, arg2)) {
            // lemma add_congr_right_rec [s : comm_semigroup A] (H1 : b = y) (H2 : a + y = z) : a + b = z
            expr_pair r_rhs = add_flatten(arg2);
            expr_pair r_flat = add_insert_flat(arg1, r_rhs.first);
            return mk_pair(r_flat.first, get_app_builder().mk_app(get_blast_arith_add_congr_right_rec_name(), {r_rhs.second, r_flat.second}));
        } else {
            return refl(e);
        }
    }

    expr_pair insert_sorted_add(expr const & e, expr const rhs) {
        expr arg1, arg2;
        if (is_add(rhs, arg1, arg2) && is_lt(arg1, e)) {
            /* e * (arg1 * <arg2>) = arg1 * (e * <arg2>) */
            expr_pair r_recurse = insert_sorted_add(e, arg2);
            // lemma add_insertion_sort [s : comm_semigroup A] (H1 : a * c = x) : a * (b * c) = b * x
            return mk_pair(get_app_builder().mk_add(m_type, arg1, r_recurse.first),
                           get_app_builder().mk_app(get_blast_arith_add_insertion_sort_name(), {arg1, r_recurse.second}));
        } else if (is_lt(rhs, e)) {
            // lemma add_comm [s : comm_semigroup A] (a b : A) : a * b = b * a
            return mk_pair(get_app_builder().mk_add(m_type, rhs, e),
                           get_app_builder().mk_app(get_add_comm_name(), {e, rhs}));
        } else {
            return refl(get_app_builder().mk_add(m_type, e, rhs));
        }
    }

    expr_pair sort_add(expr const & e) {
        expr arg1, arg2;
        if (is_add(e, arg1, arg2)) {
            // lemma add_sort_right [s : comm_semigroup A] (H1 : b = y) (H2 : a * y = z) : a * b = z
            expr_pair r_rhs = sort_add(arg2);
            expr_pair r_sort = insert_sorted_add(arg1, r_rhs.first);
            return mk_pair(r_sort.first, get_app_builder().mk_app(get_blast_arith_add_sort_right_name(), {r_rhs.second, r_sort.second}));
        } else {
            return refl(e);
        }
    }

    /* Fusing addition
       --------------------
       1. First we fuse by recursing right and applying the following rewrites:
          a. a + 0 ==> a
          b. <numeral> + <numeral> ==> <sum>
          c. <numeral> * x + <numeral> * x ==> <sum> * x
          c. <numeral> + (<numeral> + x) ==> <sum> + x
          d. <numeral> * x + (<numeral> * x + y) ==> <sum> * x + y
          When any of the <sum>s are 0, we cancel them as well
       2. If the final result is 0 + x, we simplify to x
    */
    expr_pair fuse_add(expr const & e) {
        expr_pair r1 = fuse_add_core(e);
        expr arg1, arg2;
        if (!is_add(r1.first, arg1, arg2)) {
            return r1;
        } else if (is_zero(arg1)) {
            expr_pair r2 = mk_pair(arg2, get_app_builder().mk_app(get_zero_add_name(), {arg2}));
            return join({r1, r2});
        } else {
            return r1;
        }
    }

    expr_pair fuse_add_core(expr const & e) {
        expr arg1, arg2;
        if (!is_add(e, arg1, arg2)) return refl(e);
        expr arg1_1, arg1_2, arg2_1, arg2_2, arg2_1_1, arg2_1_2;
        expr_pair r_rhs = fuse_add_core(arg2);
        if (is_zero(r_rhs.first)) {
            // lemma add_cancel_zero_right [s : add_comm_semigroup A] [s2 : has_zero A] (a : A) : b = 0 → a + b = a
            return mk_pair(arg1, get_app_builder().mk_app(get_blast_arith_add_cancel_zero_right_name(),
                                                          {arg1, r_rhs.second}));
        } else if (is_normalized_numeral(arg1) && is_normalized_numeral(r_rhs.first)) {
            // 5 + 7 ==> 12
            // lemma add_fuse_num [s : ring A] : b = x → a + x = z → a + b = z
            expr_pair r_num = normalize_numeral_expr(get_app_builder().mk_add(m_type, arg1, r_rhs.first));
            return mk_pair(r_num.first,
                           get_app_builder().mk_app(get_blast_arith_add_fuse_num_name(), {r_rhs.second, r_num.second}));
        } else if (is_mul(arg1, arg1_1, arg1_2) && is_mul(r_rhs.first, arg2_1, arg2_2) && arg1_2 == arg2_2) {
            // (5 * x) + (7 * x) ==> 12 * x
            expr_pair r_num = normalize_numeral_expr(get_app_builder().mk_add(m_type, arg1_1, arg2_1));
            if (is_zero(r_num.first)) {
                // lemma add_fuse_zero [s : ring A] : b = x * y → a + x = 0 →  (a * y) + b = 0
                return mk_pair(m_zero,
                               get_app_builder().mk_app(get_blast_arith_add_fuse_zero_name(), {r_rhs.second, r_num.second}));
            } else {
                // lemma add_fuse [s : ring A] : b = x * y → a + x = z →  (a * y) + b = z * y
                return mk_pair(get_app_builder().mk_mul(m_type, r_num.first, arg1_2),
                               get_app_builder().mk_app(get_blast_arith_add_fuse_name(), {r_rhs.second, r_num.second}));
            }
        } else if (is_normalized_numeral(arg1) && is_add(r_rhs.first, arg2_1, arg2_2) && is_normalized_numeral(arg2_1)) {
            /* 5 + (7 + _) => 12 + _ */
            expr_pair r_num = normalize_numeral_expr(get_app_builder().mk_add(m_type, arg1, arg2_1));
            if (is_zero(r_num.first)) {
                // lemma add_fuse_num_zero_left [s : ring A] : b = x + y → a + x = 0 → a + b = y
                return mk_pair(arg2_2,
                               get_app_builder().mk_app(get_blast_arith_add_fuse_num_zero_left_name(), {r_rhs.second, r_num.second}));
            } else {
                // lemma add_fuse_num_left [s : ring A] : b = x + y → a + x = z → a + b = z + y
                return mk_pair(get_app_builder().mk_add(m_type, r_num.first, arg2_2),
                               get_app_builder().mk_app(get_blast_arith_add_fuse_num_left_name(), {r_rhs.second, r_num.second}));
            }
        } else if (is_mul(arg1, arg1_1, arg1_2) && is_add(r_rhs.first, arg2_1, arg2_2)
                   && is_mul(arg2_1, arg2_1_1, arg2_1_2) && arg1_2 == arg2_1_2) {
            /* 5 * x + (7 * x + _) => 12 * x + _ */
            expr_pair r_num = normalize_numeral_expr(get_app_builder().mk_add(m_type, arg1_1, arg2_1_1));
            if (is_zero(r_num.first)) {
                // lemma add_fuse_zero_left [s : ring A] : b = x * y + z →  a + x = 0 → (a * y) + b = z := sorry
                return mk_pair(arg2_2,
                               get_app_builder().mk_app(get_blast_arith_add_fuse_zero_left_name(), {r_rhs.second, r_num.second}));
            } else {
                // lemma add_fuse_left [s : ring A] : b = x * y + z →  a + x = w → (a * y) + b = (w * y) + z
                return mk_pair(get_app_builder().mk_add(m_type, get_app_builder().mk_mul(m_type, r_num.first, arg1_2), arg2_2),
                               get_app_builder().mk_app(get_blast_arith_add_fuse_left_name(), {r_rhs.second, r_num.second}));
            }
        } else {
            // lemma add_congr_right [s : has_add A] (a : A) (H2 : b = y) : a + b = a + y
            return mk_pair(get_app_builder().mk_add(m_type, arg1, r_rhs.first),
                           get_app_builder().mk_app(get_blast_arith_add_congr_right_name(), {arg1, r_rhs.second}));
        }
    }

    expr_pair normalize_add_leaves(expr const & e) {
        expr arg1, arg2;
        if (!is_add(e, arg1, arg2)) {
            expr_pair r1 = normalize(e);
            return r1;
        } else {
            expr_pair r1 = normalize_add_leaves(arg1);
            expr_pair r2 = normalize_add_leaves(arg2);
            return mk_pair(get_app_builder().mk_add(m_type, r1.first, r2.first),
                           get_app_builder().mk_app(get_blast_arith_add_congr_name(), {r1.second, r2.second}));
        }
    }

    expr_pair add_flatten_sort_fuse(expr const & e) {
        expr_pair r_assoc = add_flatten(e);
        expr_pair r_sort = sort_add(r_assoc.first);
        expr_pair r_fuse = fuse_add(r_sort.first);
        return join({r_assoc, r_sort, r_fuse});
    }

    expr_pair normalize_add(expr const & e) {
        expr_pair r_leaves = normalize_add_leaves(e);
        expr_pair r_fuse = add_flatten_sort_fuse(r_leaves.first);
        return join({r_leaves, r_fuse});
    }

    expr_pair mul_insert_flat(expr const & e, expr const & flat_rhs) {
        expr arg1, arg2;
        expr arg2_1, arg2_2;
        if (!is_mul(e, arg1, arg2)) {
            return refl(get_app_builder().mk_mul(m_type, e, flat_rhs));
        } else if (!is_mul(arg1) && !is_mul(arg2)) {
            return mk_pair(get_app_builder().mk_mul(m_type, arg1,
                                                    get_app_builder().mk_mul(m_type, arg2, flat_rhs)),
                           get_app_builder().mk_app(get_mul_assoc_name(), {arg1, arg2, flat_rhs}));
        } else {
            expr_pair r1 = mul_insert_flat(arg2, flat_rhs);
            expr_pair r2 = mul_insert_flat(arg1, r1.first);
            return mk_pair(r2.first, get_app_builder().mk_app(get_blast_arith_mul_insert_flat_name(), {r1.second, r2.second}));
        }
    }

    expr_pair mul_flatten(expr const & e) {
        expr arg1, arg2;
        if (is_mul(e, arg1, arg2)) {
            // lemma mul_congr_right_rec [s : comm_semigroup A] (H1 : b = y) (H2 : a * y = z) : a * b = z
            expr_pair r_rhs = mul_flatten(arg2);
            expr_pair r_flat = mul_insert_flat(arg1, r_rhs.first);
            return mk_pair(r_flat.first, get_app_builder().mk_app(get_blast_arith_mul_congr_right_rec_name(), {r_rhs.second, r_flat.second}));
        } else {
            return refl(e);
        }
    }

    expr_pair insert_sorted_mul(expr const & e, expr const rhs) {
        expr arg1, arg2;
        if (is_mul(rhs, arg1, arg2) && is_lt(arg1, e)) {
            /* e * (arg1 * <arg2>) = arg1 * (e * <arg2>) */
            expr_pair r_recurse = insert_sorted_mul(e, arg2);
            // lemma mul_insertion_sort [s : comm_semigroup A] (H1 : a * c = x) : a * (b * c) = b * x
            return mk_pair(get_app_builder().mk_mul(m_type, arg1, r_recurse.first),
                           get_app_builder().mk_app(get_blast_arith_mul_insertion_sort_name(), {arg1, r_recurse.second}));
        } else if (is_lt(rhs, e)) {
            // lemma mul_comm [s : comm_semigroup A] (a b : A) : a * b = b * a
            return mk_pair(get_app_builder().mk_mul(m_type, rhs, e),
                           get_app_builder().mk_app(get_mul_comm_name(), {e, rhs}));
        } else {
            return refl(get_app_builder().mk_mul(m_type, e, rhs));
        }
    }

    expr_pair sort_mul(expr const & e) {
        expr arg1, arg2;
        if (is_mul(e, arg1, arg2)) {
            expr_pair r_rhs = sort_mul(arg2);
            expr_pair r_sort = insert_sorted_mul(arg1, r_rhs.first);
            // lemma mul_congr_right_rec [s : comm_semigroup A] (H1 : b = y) (H2 : a * y = z) : a * b = z
            return mk_pair(r_sort.first, get_app_builder().mk_app(get_blast_arith_mul_congr_right_rec_name(), {r_rhs.second, r_sort.second}));
        } else {
            return refl(e);
        }
    }

    expr_pair mul_postfuse(expr const & e) {
        expr arg1, arg2;
        if (is_mul(e, arg1, arg2) && is_zero(arg1)) {
            return mk_pair(m_zero, get_app_builder().mk_app(get_zero_mul_name(), {arg2}));
        } else {
            return refl(e);
        }
    }

    /* Normalizing monomial
       --------------------
       1. First we cancel inverses, and group and normalize the numerals
       2. If the result is a product with numeral 0, we simplify to 0
    */
    expr_pair fuse_mul(expr const & e) {
        expr_pair r1 = fuse_mul_core(e);
        expr_pair r2 = mul_postfuse(r1.first);
        return join({r1, r2});
    }

    expr_pair fuse_mul_core(expr const & e) {
        expr arg1, arg2;
        if (!is_mul(e, arg1, arg2)) return refl(e);
        expr arg2_1, arg2_2, inv;
        expr_pair r_rhs = fuse_mul_core(arg2);
        if (is_one(r_rhs.first)) {
            // lemma mul_cancel_one_right [s : comm_group A] (a : A) : b = 1 → a * b = a
            return mk_pair(arg1, get_app_builder().mk_app(get_blast_arith_mul_cancel_one_right_name(),
                                                          {arg1, r_rhs.second}));
        } else if (is_normalized_numeral(arg1) && is_normalized_numeral(r_rhs.first)) {
            // lemma mul_congr_right_rec [s : comm_semigroup A] (H1 : b = y) (H2 : a * y = z) : a * b = z
            expr_pair r_num = normalize_numeral_expr(get_app_builder().mk_mul(m_type, arg1, r_rhs.first));
            return mk_pair(r_num.first, get_app_builder().mk_app(get_blast_arith_mul_congr_right_rec_name(), {r_rhs.second, r_num.second}));
        } else if (is_inv(r_rhs.first, inv) && arg1 == inv) {
            // lemma mul_inv_cancel [s : division_ring A] : a ≠ 0 → b = a⁻¹ → a * b = 1
            expr pf = prove_nonzero(arg1);
            return mk_pair(m_one, get_app_builder().mk_app(get_blast_arith_mul_inv_cancel_name(), {pf, r_rhs.second}));
        } else if (is_mul(r_rhs.first, arg2_1, arg2_2)) {
            if (is_normalized_numeral(arg1) && is_normalized_numeral(arg2_1)) {
                // lemma mul_fuse_left [s : comm_semigroup A] (c : A) : b = x * y → a * x = z → a * b = z * y
                expr_pair r_num = normalize_numeral_expr(get_app_builder().mk_mul(m_type, arg1, arg2_1));
                return mk_pair(get_app_builder().mk_mul(m_type, r_num.first, arg2_2),
                               get_app_builder().mk_app(get_blast_arith_mul_fuse_left_name(), {r_rhs.second, r_num.second}));
            } else if (is_inv(arg2_1, inv) && arg1 == inv) {
                // lemma mul_cancel_left [s : field A] (Ha : a ≠ 0) (H : b = a⁻¹ * y) : a * b = y
                expr pf = prove_nonzero(arg1);
                return mk_pair(arg2_2, get_app_builder().mk_app(get_blast_arith_mul_cancel_left_name(),
                                                                {pf, r_rhs.second}));
            } else {
                // lemma mul_congr_right [s : has_mul A] (a : A) (H2 : b = y) : a * b = a * y
                return mk_pair(get_app_builder().mk_mul(m_type, arg1, r_rhs.first),
                               get_app_builder().mk_app(get_blast_arith_mul_congr_right_name(), {arg1, r_rhs.second}));
            }
        } else {
                // lemma mul_congr_right [s : has_mul A] (a : A) (H2 : b = y) : a * b = a * y
                return mk_pair(get_app_builder().mk_mul(m_type, arg1, r_rhs.first),
                               get_app_builder().mk_app(get_blast_arith_mul_congr_right_name(), {arg1, r_rhs.second}));
        }
    }

    expr_pair distrib_step(expr const & e, expr const & distrib_rhs) {
        lean_assert(!is_add(e));
        expr arg1, arg2;
        if (!is_add(distrib_rhs, arg1, arg2)) {
            return refl(get_app_builder().mk_mul(m_type, e, distrib_rhs));
        } else {
            // lemma mul_distrib_right [s : distrib A] : a * x = z → a * y = w →  a * (x + y) = z + w
            expr_pair r1 = distrib_step(e, arg1);
            expr_pair r2 = distrib_step(e, arg2);
            return mk_pair(get_app_builder().mk_add(m_type, r1.first, r2.first),
                           get_app_builder().mk_app(get_blast_arith_mul_distrib_right_name(), {r1.second, r2.second}));
        }
    }

    expr_pair distrib_lhs(expr const & e, expr const & distrib_rhs) {
        expr arg1, arg2;
        expr arg2_1, arg2_2;
        if (!is_add(e, arg1, arg2)) {
            return distrib_step(e, distrib_rhs);
        } else {
            // lemma mul_distrib_left [s : distrib A] : a * x = y → b * x = z → (a + b) * x = y + z
            expr_pair r1 = distrib_lhs(arg1, distrib_rhs);
            expr_pair r2 = distrib_lhs(arg2, distrib_rhs);
            return mk_pair(get_app_builder().mk_add(m_type, r1.first, r2.first),
                           get_app_builder().mk_app(get_blast_arith_mul_distrib_left_name(), {r1.second, r2.second}));
        }
    }

    expr_pair distrib(expr const & e) {
        expr arg1, arg2;
        if (!is_mul(e, arg1, arg2)) return normalize(e);
        expr_pair r_lhs = distrib(arg1);
        expr_pair r_rhs = distrib(arg2);
        expr_pair r_distrib = distrib_lhs(r_lhs.first, r_rhs.first);
        // lemma mul_congr_rec [s : comm_semigroup A] (H1 : a = x) (H2 : b = y) (H3 : x * y = z) : a * b = z
        return mk_pair(r_distrib.first,
                       get_app_builder().mk_app(get_blast_arith_mul_congr_rec_name(), {r_lhs.second, r_rhs.second, r_distrib.second}));
    }

    expr_pair mul_flatten_sort_fuse(expr const & e) {
        expr_pair r_assoc = mul_flatten(e);
        expr_pair r_sort = sort_mul(r_assoc.first);
        expr_pair r_cancel = fuse_mul(r_sort.first);
        return join({r_assoc, r_sort, r_cancel});
    }

    expr_pair normalize_som(expr const & e) {
        expr_pair r = normalize_som_core(e);
        expr_pair r_fuse = add_flatten_sort_fuse(r.first);
        return join({r, r_fuse});
    }

    expr_pair normalize_som_core(expr const & e) {
        expr arg1, arg2;
        if (!is_add(e, arg1, arg2)) {
            return mul_flatten_sort_fuse(e);
        } else {
            expr_pair r1 = normalize_som_core(arg1);
            expr_pair r2 = normalize_som_core(arg2);
            return mk_pair(get_app_builder().mk_add(m_type, r1.first, r2.first),
                           get_app_builder().mk_app(get_blast_arith_add_congr_name(), {r1.second, r2.second}));
        }
    }

    expr_pair normalize_mul(expr const & e) {
        expr_pair r_distrib = distrib(e);
        expr_pair r_som = normalize_som(r_distrib.first);
        return join({r_distrib, r_som});
    }

    expr_pair normalize_neg_core(expr const & neg_e) {
        expr arg, arg1, arg2;
        if (is_mul(neg_e, arg1, arg2)) {
            // lemma neg_num_mul [s : ring A] (y : A) (H : -x = z) : - (x * y) = z * y
            expr_pair r_numeral = normalize_numeral_expr(get_app_builder().mk_neg(m_type, arg1));
            return mk_pair(get_app_builder().mk_mul(m_type, r_numeral.first, arg2),
                           get_app_builder().mk_app(get_blast_arith_neg_num_mul_name(), {arg2, r_numeral.second}));
        } else if (is_add(neg_e, arg1, arg2)) {
            // lemma neg_add [s : add_group A] (H1 : - x = z) (H2 : -y = w) : - (x + y) = z + w
            expr_pair r_lhs = normalize_neg_core(arg1);
            expr_pair r_rhs = normalize_neg_core(arg2);
            return mk_pair(get_app_builder().mk_add(m_type, r_lhs.first, r_rhs.first),
                           get_app_builder().mk_app(get_blast_arith_neg_add_name(), {r_lhs.second, r_rhs.second}));
        } else {
            lean_assert(is_normalized_numeral(neg_e));
            return normalize_numeral_expr(get_app_builder().mk_neg(m_type, neg_e));
        }
    }

    expr_pair normalize_neg(expr const & neg_e) {
        // lemma neg_congr [s : add_group A] (H1 : a = b) (H2 : -b = c) : - a = c
        expr_pair r1 = normalize(neg_e);
        expr_pair r2 = normalize_neg_core(r1.first);
        return mk_pair(r2.first, get_app_builder().mk_app(get_blast_arith_neg_congr_name(), {r1.second, r2.second}));
    }

    expr_pair normalize_inv_core(expr const & inv_e) {
        expr arg, arg1, arg2;
        if (is_normalized_numeral(inv_e)) {
            return normalize_numeral_expr(get_app_builder().mk_inv(m_type, inv_e));
        } else if (is_mul(inv_e, arg1, arg2)) {
            if (is_one(arg1) && !is_inv(arg2) && !is_mul(arg2)) {
                // lemma inv_mul_one [s : field A] : (1 * y)⁻¹ = 1 * y⁻¹
                // (not necessary, but lets us avoid unnecessary non-zero proofs)
                return mk_pair(get_app_builder().mk_mul(m_type, m_one, get_app_builder().mk_inv(m_type, arg2)),
                               get_app_builder().mk_app(get_blast_arith_inv_mul_one_name(), {arg2}));
            } else {
                // lemma inv_mul [s : field A] (Hx : x₁ ≠ 0) (Hy : y₁ ≠ 0) (H1 : x₁⁻¹ = x₂) (H2 : y₁⁻¹ = y₂) : (x₁ * y₁)⁻¹ = x₂ * y₂
                expr pf_lhs = is_normalized_numeral(arg1) ? prove_ne_zero(arg1, m_type) : prove_nonzero(arg1);
                expr pf_rhs = prove_nonzero(arg2);
                expr_pair r_lhs = normalize_inv_core(arg1);
                expr_pair r_rhs = normalize_inv_core(arg2);
                return mk_pair(get_app_builder().mk_mul(m_type, r_lhs.first, r_rhs.first),
                               get_app_builder().mk_app(get_blast_arith_inv_mul_name(), {pf_lhs, pf_rhs, r_lhs.second, r_rhs.second}));
            }
        } else if (is_inv(inv_e, arg)) {
            //  theorem division_ring.inv_inv (H : a ≠ 0) : (a⁻¹)⁻¹ = a
            expr pf = prove_nonzero(arg);
            return mk_pair(arg, get_app_builder().mk_app(get_division_ring_inv_inv_name(), {pf}));
        } else {
            return refl(get_app_builder().mk_inv(m_type, inv_e));
        }
    }

    expr_pair normalize_inv(expr const & inv_e) {
        // lemma inv_congr [s : division_ring A] (H1 : a = b) (H2 : b⁻¹ = c) : a⁻¹ = c
        expr_pair r1 = normalize(inv_e);
        expr_pair r2 = normalize_inv_core(r1.first);
        return mk_pair(r2.first, get_app_builder().mk_app(get_blast_arith_inv_congr_name(), {r1.second, r2.second}));
    }

    expr_pair normalize_blackbox(expr const & e) {
        // lemma one_mul_rev [s : monoid A] (a : A) : a = 1 * a
        return mk_pair(get_app_builder().mk_mul(m_type, m_one, e),
                       get_app_builder().mk_app(get_blast_arith_one_mul_rev_name(), {e}));
    }

    /* Normal form:
       ------------
       Monomial: a non-zero numeral times a (possibly empty) product of black-boxes and their inverses
       Polynomial: a sum of monomials
    */
    expr_pair normalize(expr const & e) {
        m_num_steps++;
        if (m_num_steps > m_max_steps)
            throw exception(sstream() << "arith::normalize failed, maximum number of steps (" << m_max_steps << ") exceeded");

        expr arg;
        if (is_numeral_expr(e)) {
            lean_trace(*g_normalize_trace_name, tout() << "normalize::numeral: " << e << "\n";);
            return normalize_numeral_expr(e);
        } else if (is_inv(e, arg)) {
            lean_trace(*g_normalize_trace_name, tout() << "normalize::inv: " << e << "\n";);
            return normalize_inv(arg);
        } else if (is_mul(e)) {
            lean_trace(*g_normalize_trace_name, tout() << "normalize::mul: " << e << "\n";);
            return normalize_mul(e);
        } else if (is_neg(e, arg)) {
            lean_trace(*g_normalize_trace_name, tout() << "normalize::neg: " << e << "\n";);
            return normalize_neg(arg);
        } else if (is_add(e)) {
            lean_trace(*g_normalize_trace_name, tout() << "normalize::add: " << e << "\n";);
            return normalize_add(e);
        } else {
            lean_trace(*g_normalize_trace_name, tout() << "normalize::unknown: " << e << "\n";);
            return normalize_blackbox(e);
        }
    }
public:
    normalize_fn(expr const & type): m_type(type) {
        m_zero = get_app_builder().mk_zero(type);
        m_one = get_app_builder().mk_one(type);
        m_negative_one = get_app_builder().mk_neg(type, m_one);
    }
    expr_pair operator()(expr const & e) { return normalize(e); }
    list<expr> get_placeholders() const {
        list<expr> placeholders;
        for (auto const & p : m_placeholders) { placeholders = cons(p.second, placeholders); }
        return placeholders;
    }
};

/* Setup and teardown */
void initialize_normalize() {
    g_normalize_trace_name = new name{"blast", "arith", "normalize"};
    g_normalize_error_trace_name = new name{"blast", "arith", "normalize", "error"};
    register_trace_class(*g_normalize_trace_name);
    register_trace_class(*g_normalize_error_trace_name);

    g_arith_normalize_max_steps     = new name{"blast", "arith", "normalize", "max_steps"};
    register_unsigned_option(*g_arith_normalize_max_steps, LEAN_DEFAULT_ARITH_NORMALIZE_MAX_STEPS,
                             "(debug) max allowed steps in arithmetic normalization");
}

void finalize_normalize() {
    delete g_arith_normalize_max_steps;
    delete g_normalize_trace_name;
}

/* Entry point */
pair<result, list<expr> > arith::normalize(expr const & e, expr const & type) {
    auto fn = normalize_fn(type);
    expr_pair r = fn(e);
    if (r.first == e) return mk_pair(result(e), fn.get_placeholders());
    else return mk_pair(result(r.first, r.second), fn.get_placeholders());
}

pair<expr, list<expr> > arith::normalize_prove_eq(expr const & e1, expr const & e2, expr const & type) {
    auto fn = normalize_fn(type);
    expr_pair ep1 = fn(e1);
    expr_pair ep2 = fn(e2);
    result r1 = ep1.first == e1 ? result(ep1.first) : result(ep1.first, ep1.second);
    result r2 = ep2.first == e2 ? result(ep2.first) : result(ep2.first, ep2.second);
    lean_assert(r1.first == r2.first);
    if (r1.get_new() != r2.get_new()) {
        lean_trace(*g_normalize_trace_name, tout() << "normalize_prove_eq failed: " << ppb(r1.get_new()) << " != " << ppb(r2.get_new()) << "\n";);
        lean_trace(*g_normalize_trace_name, tout() << "originals: " << ppb(e1) << " != " << ppb(e2) << "\n";);
        throw exception("normalize_prove_eq failed");
    }
    if (r1.has_proof() && r2.has_proof()) {
        return mk_pair(get_app_builder().mk_eq_trans(r1.get_proof(),
                                                     get_app_builder().mk_eq_symm(r2.get_proof())),
                       fn.get_placeholders());
    } else if (r1.has_proof()) {
        return mk_pair(r1.get_proof(), fn.get_placeholders());
    } else if (r2.has_proof()) {
        return mk_pair(get_app_builder().mk_eq_symm(r2.get_proof()), fn.get_placeholders());
    } else {
        return mk_pair(get_app_builder().mk_eq_refl(r1.get_new()), fn.get_placeholders());
    }
}


}}
