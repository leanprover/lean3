/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Robert Y. Lewis
*/
#include "library/norm_num.h"
namespace lean {
static name * g_one     = nullptr;
static name * g_zero    = nullptr;
static name * g_bitone  = nullptr;
static name * g_bitzero = nullptr;
static name * g_add     = nullptr;
static name * g_add1    = nullptr;
static name * g_mul     = nullptr;
static name * g_div     = nullptr;
static name * g_sub     = nullptr;
static name * g_bit0_add_bit0 = nullptr;
static name * g_bit1_add_bit0 = nullptr;
static name * g_bit0_add_bit1 = nullptr;
static name * g_bit1_add_bit1 = nullptr;
static name * g_bin_add_0     = nullptr;
static name * g_bin_0_add     = nullptr;
static name * g_bin_add_1     = nullptr;
static name * g_1_add_bit0    = nullptr;
static name * g_bit0_add_1    = nullptr;
static name * g_bit1_add_1    = nullptr;
static name * g_1_add_bit1    = nullptr;
static name * g_one_add_one   = nullptr;
static name * g_add1_bit0     = nullptr;
static name * g_add1_bit1     = nullptr;
static name * g_add1_zero     = nullptr;
static name * g_add1_one      = nullptr;
static name * g_subst_sum     = nullptr;
static name * g_mk_cong       = nullptr;
static name * g_mk_eq         = nullptr;

static bool is_numeral_aux(expr const & e, bool is_first) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    if (!is_constant(f)) {
      return false;
    }
    if (const_name(f) == *g_one) {
        return args.size() == 2;
    } else if (const_name(f) == *g_zero) {
        return is_first && args.size() == 2;
    } else if (const_name(f) == *g_bitone || const_name(f) == *g_bitzero) {
        return args.size() == 3 && is_numeral_aux(args[2], false);
    }
    return false;
}

bool norm_num_context::is_numeral(expr const & e) const {
    return is_numeral_aux(e, true);
}

bool is_bit0 (expr const & e) {
    return is_constant(e) && const_name(e) == *g_bitzero;
}

bool is_bit1 (expr const & e) {
    return is_constant(e) && const_name(e) == *g_bitone;
}

bool is_zero (expr const & e) {
    return is_constant(e) && const_name(e) == *g_zero;
}

bool is_one (expr const & e) {
    return is_constant(e) && const_name(e) == *g_one;
}


expr norm_num_context::mk_const(name const & n) {
    return mk_constant(n, m_lvls);
}

expr norm_num_context::mk_cong(expr const & op, expr const & type, expr const & a, expr const & b, expr const & eq) {
    return mk_app({mk_const(*g_mk_cong), type, op, a, b, eq});
}

pair<expr, expr> norm_num_context::mk_norm(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f)) {
        throw exception("cannot take norm of nonconstant");
    }
    m_lvls = const_levels(f);
    //std::cout << "here now " << std::to_string(args.size())  << "\n";
    //std::cout << " " << const_name(f) << " " << *g_add << "\n";
    if (const_name(f) == *g_add && args.size() == 4) {
        //std::cout << "we are adding " << args[2] << " and " << args[3] << ". time to normalize.\n";
        auto lhs_p = mk_norm(args[2]);
	auto rhs_p = mk_norm(args[3]);
	//std::cout << "normalized lhs and rhs. \n ";
	//std::cout << " started with " << args[2] << " and " << args[3]<<",\n";
	//std::cout << " ended with " << lhs_p.first << " and " << rhs_p.first << "\n";
        auto add_p = mk_norm_add(lhs_p.first, rhs_p.first);
	//std::cout << "adding " << lhs_p.first << " to " << rhs_p.first << " gave " << add_p.first << ".\n";
	expr prf = mk_app({mk_const(*g_subst_sum), args[0], args[1], args[2], args[3], 
	                  lhs_p.first, rhs_p.first, add_p.first, lhs_p.second, rhs_p.second, add_p.second});
	return pair<expr, expr>(add_p.first, prf);
    } else if ((const_name(f) == *g_bitzero || const_name(f) == *g_bitone) && args.size() == 3) {
        auto arg = mk_norm(args[2]);
	expr rv = mk_app({f, args[0], args[1], arg.first});
	expr prf = mk_cong(mk_app({f, args[0], args[1]}), args[0], args[2], arg.first, arg.second);
	return pair<expr, expr>(rv, prf);
    } else if ((const_name(f) == *g_zero || const_name(f) == *g_one) && args.size() == 2) {
        return pair<expr, expr>(e, mk_app({mk_const(*g_mk_eq), args[0], e}));
    } else {
        std::cout << "error with name " << const_name(f) << " and size " << args.size() << ".\n";
	std::cout << "args were " << args[0] << ", " << args[1] << ", " << args[2] << ", " << args[3] << "\n";
        throw exception("mk_norm found unrecognized combo ");
    }
    // TODO(Rob): cases for mul, sub, div
}

// returns <t, p> such that p is a proof that lhs + rhs = t. (is that true? symm?)
pair<expr, expr> norm_num_context::mk_norm_add(expr const & lhs, expr const & rhs) { 
    /*buffer<expr> args;
    expr f_add = get_app_args(e, args);
    expr lhs = args[2];
    expr rhs = args[3];*/
    buffer<expr> args_lhs;
    buffer<expr> args_rhs;
    expr lhs_head = get_app_args (lhs, args_lhs);
    expr rhs_head = get_app_args (rhs, args_rhs);
    if (!is_constant(lhs_head) || !is_constant(rhs_head)) {
        throw exception("cannot take norm_add of nonconstant");
    }
    auto type = args_lhs[0];
    auto typec = args_lhs[1];
    expr rv;
    expr prf;
    //std::cout << "we are adding " << lhs_head << " to " << rhs_head << ".\n";
    if (is_bit0(lhs_head) && is_bit0(rhs_head)) {
        auto p = mk_norm_add(args_lhs[2], args_rhs[2]);
	rv = mk_app(lhs_head, type, typec, p.first);
	prf = mk_app({mk_const(*g_bit0_add_bit0), type, typec, args_lhs[2], args_rhs[2], p.first, p.second});
    } else if (is_bit0(lhs_head) && is_bit1(rhs_head)) {
        auto p = mk_norm_add(args_lhs[2], args_rhs[2]);
	rv = mk_app(rhs_head, type, typec, p.first);
	prf = mk_app({mk_const(*g_bit0_add_bit1), type, typec, args_lhs[2], args_rhs[2], p.first, p.second});
    } else if (is_bit0(lhs_head) && is_one(rhs_head)) {
        rv = mk_app({mk_const(*g_bitone), type, typec, args_lhs[2]});
        prf = mk_app({mk_const(*g_bit0_add_1), type, typec, args_lhs[2]});
    } else if (is_bit1(lhs_head) && is_bit0(rhs_head)) {
        auto p = mk_norm_add(args_lhs[2], args_rhs[2]);
	rv = mk_app(lhs_head, type, typec, p.first);
	prf = mk_app({mk_const(*g_bit1_add_bit0), type, typec, args_lhs[2], args_rhs[2], p.first, p.second});
    } else if (is_bit1(lhs_head) && is_bit1(rhs_head)) {
        expr f_add = mk_app({mk_const(*g_add), type, typec});
        expr add1 = mk_app({mk_const(*g_add1), type, typec, mk_app({f_add, type, typec, args_lhs[2], args_rhs[2]})});
	auto p = mk_norm_add1(add1);
	rv = mk_app({mk_const(*g_bitzero), type, typec, p.first});
	prf = mk_app({mk_const(*g_bit1_add_bit1), type, typec, args_lhs[2], args_rhs[2], p.first, p.second});
    } else if (is_bit1(lhs_head) && is_one(rhs_head)) {
        expr add1 = mk_app({mk_const(*g_add1), type, typec, lhs});
	auto p = mk_norm_add1(add1);
	rv = p.first;
	prf = mk_app({mk_const(*g_bit1_add_1), type, typec, args_lhs[2], p.first, p.second});
    } else if (is_one(lhs_head) && is_bit0(rhs_head)) {
        rv = mk_app({mk_const(*g_bitone), type, typec, args_rhs[2]});
        prf = mk_app({mk_const(*g_1_add_bit0), type, typec, args_rhs[2]});
    } else if (is_one(lhs_head) && is_bit1(rhs_head)) {
        expr add1 = mk_app({mk_const(*g_add1), type, typec, rhs});
	auto p = mk_norm_add1(add1);
	rv = p.first;
	prf = mk_app({mk_const(*g_1_add_bit1), type, typec, args_rhs[2], p.first, p.second});
    } else if (is_one(lhs_head) && is_one(rhs_head)) {
        rv = mk_app({mk_const(*g_bitzero), type, typec, mk_app({mk_const(*g_one), type, typec})});
	prf = mk_app({mk_const(*g_one_add_one), type, typec});
    } else if (is_zero(lhs_head)) {
        rv = rhs_head;
        prf = mk_app({mk_const(*g_bin_0_add), type, typec, rhs_head});
    } else if (is_zero(rhs_head)) {
        rv = lhs_head;
        prf = mk_app({mk_const(*g_bin_add_0), type, typec, lhs_head});
    }
    else {
      throw exception("mk_norm_add got malformed args");
    }
    return pair<expr, expr>(rv, prf);
}

pair<expr, expr> norm_num_context::mk_norm_add1(expr const & e) {
    // TODO(Rob)
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr p = args[2];
    buffer<expr> ne_args;
    expr ne = get_app_args(p, ne_args);
    expr rv;
    expr prf;
    if (is_bit0(ne)) {
        rv = mk_app({mk_const(*g_bitone), args[0], args[1], ne_args[2]});
	prf = mk_app({mk_const(*g_add1_bit0), args[0], args[1], ne_args[2]});
    } else if (is_bit1(ne)) {
        auto np = mk_norm_add1(mk_app({mk_const(*g_add1), args[0], args[1], ne_args[2]}));
	rv = mk_app({mk_const(*g_bitzero), args[0], args[1], np.first});
	prf = mk_app({mk_const(*g_add1_bit1), args[0], args[1], ne_args[2], np.first, np.second});
    } else if (is_zero(ne)) {
        rv = mk_app({mk_const(*g_one), args[0], args[1]});
	prf = mk_app({mk_const(*g_add1_zero), args[0], args[1]});
    } else if (is_one(ne)) {
        rv = mk_app({mk_const(*g_bitzero), args[0], args[1], mk_app({mk_const(*g_one), args[0], args[1]})});
	prf = mk_app({mk_const(*g_add1_one), args[0], args[1]});
    } else {
        throw exception("malformed add1");
    }
    return pair<expr, expr>(rv, prf);
}

pair<expr, expr> norm_num_context::mk_norm_mul(expr const &, expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet -- mk_norm_mul");
}

pair<expr, expr> norm_num_context::mk_norm_div(expr const &, expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet -- mk_norm_div");
}

pair<expr, expr> norm_num_context::mk_norm_sub(expr const &, expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet -- mk_norm_sub");
}

void initialize_norm_num() {
  g_one     = new name("one");
  g_zero    = new name("zero");
  g_bitone  = new name("bit1");
  g_bitzero = new name("bit0");
  g_add     = new name("add"); //name{"algebra", "has_add", "add"};
  g_add1    = new name("add1");
  g_mul     = new name("mul");
  g_div     = new name("div");
  g_sub     = new name("sub");
  g_bit0_add_bit0 = new name("bit0_add_bit0_helper");
  g_bit1_add_bit0 = new name("bit1_add_bit0_helper");
  g_bit0_add_bit1 = new name("bit0_add_bit1_helper");
  g_bit1_add_bit1 = new name("bit1_add_bit1_helper");
  g_bin_add_0     = new name("bin_add_zero");
  g_bin_0_add     = new name("bin_zero_add");
  g_bin_add_1     = new name("bin_add_one");
  g_1_add_bit0    = new name("one_add_bit0");
  g_bit0_add_1    = new name("bit0_add_one");
  g_bit1_add_1    = new name("bit1_add_one_helper");
  g_1_add_bit1    = new name("one_add_bit1_helper");
  g_one_add_one   = new name("one_add_one");
  g_add1_bit0     = new name("add1_bit0");
  g_add1_bit1     = new name("add1_bit1_helper");
  g_add1_zero     = new name("add1_zero");
  g_add1_one      = new name("add1_one");
  g_subst_sum     = new name("subst_into_sum");
  g_mk_cong       = new name("mk_cong");
  g_mk_eq         = new name("mk_eq");
}

void finalize_norm_num() {
  delete g_one;
  delete g_zero;
  delete g_bitone;
  delete g_bitzero;
  delete g_add;
  delete g_add1;
  delete g_mul;
  delete g_div;
  delete g_sub;
  delete g_bit0_add_bit0;
  delete g_bit1_add_bit0;
  delete g_bit0_add_bit1;
  delete g_bit1_add_bit1;
  delete g_bin_add_0;
  delete g_bin_0_add;
  delete g_bin_add_1;
  delete g_1_add_bit0;
  delete g_bit0_add_1;
  delete g_bit1_add_1;
  delete g_1_add_bit1;
  delete g_one_add_one;
  delete g_add1_bit0;
  delete g_add1_bit1;
  delete g_add1_zero;
  delete g_add1_one;
  delete g_subst_sum;
  delete g_mk_cong;
  delete g_mk_eq;
}
}
