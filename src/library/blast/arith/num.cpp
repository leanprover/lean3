/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <iostream>
#include "library/blast/arith/num.h"
#include "library/blast/blast_exception.h"
#include "library/blast/trace.h"
#include "library/blast/blast.h"
#include "library/constants.h"
#include "library/num.h"
#include "library/norm_num.h"

namespace lean {
namespace blast {

static name * g_num_trace_name = nullptr;
static name * g_num_trace_simplify_name = nullptr;

/* Convert to Lean expressions */
expr mpz_to_expr_core(mpz const & n, expr const & A) {
    lean_assert(n > 0);
    if (n == 1) return get_app_builder().mk_one(A);
    expr rec = mpz_to_expr_core(n/2, A);
    if (n % mpz(2) == 1) return get_app_builder().mk_bit1(A, rec);
    else return get_app_builder().mk_bit0(A, rec);
}

expr mpz_to_expr(mpz const & n, expr const & A) {
    if (n == 0) return get_app_builder().mk_zero(A);
    else if (n < 0) return get_app_builder().mk_neg(A, mpz_to_expr_core(neg(n), A));
    else return mpz_to_expr_core(n, A);
}

expr mpq_to_expr(mpq const & n, expr const & A) {
    if (n == 0) {
        return get_app_builder().mk_zero(A);
    } else if (n < 0) {
        return get_app_builder().mk_neg(A, mpq_to_expr(neg(n), A));
    } else if (n.is_integer()) {
        return mpz_to_expr_core(n.get_numerator(), A);
    } else if (n.get_numerator() == 1) {
        return get_app_builder().mk_inv(A, mpz_to_expr(n.get_denominator(), A));
    } else {
        return get_app_builder().mk_mul(A,
                                        mpz_to_expr(n.get_numerator(), A),
                                        get_app_builder().mk_inv(A, mpz_to_expr(n.get_denominator(), A)));
    }
}

/* Convert from Lean expressions */
mpq expr_to_mpq(expr const & e) {
    expr arg, arg1, arg2;
    if (auto n = to_num(e)) {
        return mpq(*n);
    } else if (is_add(e, arg1, arg2)) {
        return expr_to_mpq(arg1) + expr_to_mpq(arg2);
    } else if (is_mul(e, arg1, arg2)) {
        return expr_to_mpq(arg1) * expr_to_mpq(arg2);
    } else if (is_inv(e, arg)) {
        return inv(expr_to_mpq(arg));
    } else if (is_neg(e, arg)) {
        return neg(expr_to_mpq(arg));
    } else {
        lean_trace(*g_num_trace_name, tout() << "expression in expr_to_mpq is malformed: " << ppb(e) << "\n";);
        throw blast_exception("expression in expr_to_mpq is malfomed", e);
    }
}

/* Prove positive */
/*
  theorem pos_bit0 {A : Type} [s : linear_ordered_comm_ring A] (a : A) (H : 0 < a) : 0 < bit0 a := sorry
  theorem pos_bit1 {A : Type} [s : linear_ordered_comm_ring A] (a : A) (H : 0 < a) : 0 < bit1 a := sorry
  theorem zero_lt_one {A : Type} [s : linear_ordered_comm_ring A] : 0 < 1 := sorry
*/
pair<expr, expr> prove_positive_core(mpz const & n, expr const & A) {
    lean_assert(n > 0);
    if (n == 1) {
        expr one = get_app_builder().mk_one(A);
        expr pf = get_app_builder().mk_zero_lt_one(A);
        return mk_pair(one, pf);
    } else if (n % mpz(2) == 1) {
        pair<expr, expr> rec = prove_positive_core(n/2, A);
        expr new_num = get_app_builder().mk_bit1(A, rec.first);
        expr new_pf = get_app_builder().mk_app(get_ordered_arith_pos_bit1_name(), {rec.first, rec.second});
        return mk_pair(new_num, new_pf);
    } else {
        pair<expr, expr> rec = prove_positive_core(n/2, A);
        expr new_num = get_app_builder().mk_bit0(A, rec.first);
        expr new_pf = get_app_builder().mk_app(get_ordered_arith_pos_bit0_name(), {rec.first, rec.second});
        return mk_pair(new_num, new_pf);
    }
}

expr prove_positive(mpz const & n, expr const & A) {
    return prove_positive_core(n, A).second;
}

expr prove_positive(mpq const & n, expr const & A) {
    if (n.is_integer()) {
        return prove_positive(n.get_numerator(), A);
    } else {
        expr pf_a = prove_positive(n.get_numerator(), A);
        expr pf_b = prove_positive(n.get_denominator(), A);
        return get_app_builder().mk_app(get_ordered_arith_mulinv_pos_of_pos_pos_name(), {pf_a, pf_b});
    }
}

/* Prove a contradiction */
/*
  theorem zero_not_lt_zero [s : linear_ordered_comm_ring A] : 0 < 0 → false := sorry
  theorem pos_not_neg [s : linear_ordered_comm_ring A] (c : A) : 0 < c → 0 < - c → false := sorry
  theorem pos_not_nonpos [s : linear_ordered_comm_ring A] (c : A) : 0 < c → 0 ≤ - c → false := sorry
*/

// TODO(dhs): clean this up, stop synthesizing and checking everywhere
expr prove_zero_not_lt_zero(expr const & A) {
    return get_app_builder().mk_zero_not_lt_zero(A);
}

expr prove_zero_not_lt_neg(expr const & A, mpq const & nc) {
    return get_app_builder().mk_app(get_ordered_arith_zero_not_lt_neg_name(), 4, {prove_positive(neg(nc), A)});
}

expr prove_zero_not_le_neg(expr const & A, mpq const & nc) {
    return get_app_builder().mk_app(get_ordered_arith_zero_not_le_neg_name(), 4, {prove_positive(neg(nc), A)});
}

/* Note: this must be called on a numeral, not any numeral expression */
expr prove_num_positive(expr const & e, expr const & type) {
    expr arg;
    if (is_bit0(e, arg)) {
        return get_app_builder().mk_app(get_ordered_arith_pos_bit0_name(), prove_num_positive(arg, type));
    } else if (is_bit1(e, arg)) {
        return get_app_builder().mk_app(get_ordered_arith_pos_bit1_name(), prove_num_positive(arg, type));
    } else if (is_one(e)) {
        return get_app_builder().mk_zero_lt_one(type);
    } else {
        lean_trace(*g_num_trace_name, tout() << "prove_num_positive called on zero or non_numeral: " << ppb(e) << "\n";);
        throw exception("prove_num_positive called on zero or non_numeral");
    }
}

/* Note: must be called on a normalized numeral */
expr prove_ne_zero(expr const & e, expr const & type) {
    expr neg_e, inv_e, num, den;
    if (is_neg(e, neg_e)) {
        return get_app_builder().mk_app(get_ordered_arith_nonzero_of_neg_name(), 4, {prove_ne_zero(neg_e, type)});
    } else if (is_inv(e, inv_e)) {
        return get_app_builder().mk_app(get_inv_ne_zero_name(), 4, {prove_ne_zero(inv_e, type)});
    } else if (is_mulinv(e, num, den)) {
        expr pf_num_ne_zero = prove_ne_zero(num, type);
        expr pf_den_ne_zero = prove_ne_zero(den, type);
        return get_app_builder().mk_app(get_norm_num_mulinv_ne_zero_of_ne_zero_ne_zero_name(), 6, {pf_num_ne_zero, pf_den_ne_zero});
    } else  {
        return get_app_builder().mk_app(get_ordered_arith_nonzero_of_pos_name(), 4, {prove_num_positive(e, type)});
    }
}

/* Testers */
bool is_mulinv(expr const & e) {
    expr arg1, arg2;
    return is_mul(e, arg1, arg2) && is_inv(arg2);
}

bool is_mulinv(expr const & e, expr & n, expr & d) {
    expr arg1, arg2, arg;
    if (is_mul(e, arg1, arg2) && is_inv(arg2, arg)) {
        n = arg1;
        d = arg;
        return true;
    } else {
        return false;
    }
}

bool is_numeral_expr(expr const & e) {
    if (is_num(e)) return true;
    expr arg, arg1, arg2;
    if (is_add(e, arg1, arg2)) return is_numeral_expr(arg1) && is_numeral_expr(arg2);
    else if (is_mul(e, arg1, arg2)) return is_numeral_expr(arg1) && is_numeral_expr(arg2);
    else if (is_neg(e, arg)) return is_numeral_expr(arg);
    else if (is_inv(e, arg)) return is_numeral_expr(arg);
    else return false;
}

/* Normalization */

simp::result normalize_numeral_expr(expr const & e) {
    /* We need to wrap the result of `mk_norm_num` to return `inv` instead of `div` */
    blast_tmp_type_context tmp_tctx;
    expr_pair r = mk_norm_num(*tmp_tctx, e);
    buffer<expr> args;
    expr f = get_app_args(r.first, args);
    expr val, pf;
    if (is_constant(f) && const_name(f) == get_div_name()) {
        lean_assert(args.size() == 4);
        if (is_one(args[2])) {
            // lemma eq_inv_of_eq_div_helper [s : field A] (a b : A) (H : a = 1 / b) : a = b⁻¹
            val = get_app_builder().mk_inv(args[0], args[3]);
            pf = get_app_builder().mk_app(get_norm_num_eq_inv_of_eq_div_helper_name(), {r.second});
        } else {
            // lemma eq_mulinv_of_eq_div_helper [s : field A] (a b c : A) (H : a = b / c) : a = b * c⁻¹
            val = get_app_builder().mk_mul(args[0], args[2], get_app_builder().mk_inv(args[0], args[3]));
            pf = get_app_builder().mk_app(get_norm_num_eq_mulinv_of_eq_div_helper_name(), {r.second});
        }
    } else {
        val = r.first;
        pf = r.second;
    }
    // TODO(dhs): avoid the equality check
    if (val == e) {
        lean_trace(*g_num_trace_name, tout() << "normalize_numeral_expr: " << ppb(e) << " ==> (refl)\n";);
        return simp::result(e);
    } else {
        lean_trace(*g_num_trace_name, tout() << "normalize_numeral_expr: " << ppb(e) << " ==> " << ppb(val) << "\n";);
        return simp::result(val, pf);
    }
}

/* Setup and teardown */
void initialize_num() {
    g_num_trace_name = new name{"blast", "num"};
    g_num_trace_simplify_name = new name{"blast", "num", "simplify"};
    register_trace_class(*g_num_trace_name);
    register_trace_class(*g_num_trace_simplify_name);
}

void finalize_num() {
    delete g_num_trace_name;
}

}}
