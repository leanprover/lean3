/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/expr.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "kernel/for_each_fn.h"
#include "library/generic_exception.h"
#include "library/kernel_serializer.h"
#include "library/io_state_stream.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/tactic/inversion_tactic.h"

namespace lean {
static name * g_equations_name    = nullptr;
static name * g_equation_name     = nullptr;
static name * g_decreasing_name   = nullptr;
static name * g_inaccessible_name = nullptr;
static std::string * g_equations_opcode  = nullptr;
static std::string * g_equation_opcode   = nullptr;
static std::string * g_decreasing_opcode = nullptr;

[[ noreturn ]] static void throw_eqs_ex() { throw exception("unexpected occurrence of 'equations' expression"); }
[[ noreturn ]] static void throw_eq_ex() { throw exception("unexpected occurrence of 'equation' expression"); }

class equations_macro_cell : public macro_definition_cell {
    unsigned m_num_fns;
public:
    equations_macro_cell(unsigned num_fns):m_num_fns(num_fns) {}
    virtual name get_name() const { return *g_equations_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const { throw_eqs_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_eqs_ex(); }
    virtual void write(serializer & s) const { s << *g_equations_opcode << m_num_fns; }
    unsigned get_num_fns() const { return m_num_fns; }
};

class equation_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_equation_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const {
        expr dummy = mk_Prop();
        return mk_pair(dummy, constraint_seq());
    }
    virtual optional<expr> expand(expr const &, extension_context &) const {
        expr dummy = mk_Type();
        return some_expr(dummy);
    }
    virtual void write(serializer & s) const { s.write_string(*g_equation_opcode); }
};

class decreasing_macro_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception("invalid 'decreasing' expression, incorrect number of arguments");
    }
public:
    decreasing_macro_cell() {}
    virtual name get_name() const { return *g_decreasing_name; }
    virtual pair<expr, constraint_seq> get_type(expr const & m, extension_context & ctx) const {
        check_macro(m);
        return ctx.infer_type(macro_arg(m, 0));
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const { s.write_string(*g_decreasing_opcode); }
};

static macro_definition * g_equation   = nullptr;
static macro_definition * g_decreasing = nullptr;

bool is_equation(expr const & e) { return is_macro(e) && macro_def(e) == *g_equation; }

bool is_lambda_equation(expr const & e) {
    if (is_lambda(e))
        return is_lambda_equation(binding_body(e));
    else
        return is_equation(e);
}

expr const & equation_lhs(expr const & e) { lean_assert(is_equation(e)); return macro_arg(e, 0); }
expr const & equation_rhs(expr const & e) { lean_assert(is_equation(e)); return macro_arg(e, 1); }
expr mk_equation(expr const & lhs, expr const & rhs) {
    expr args[2] = { lhs, rhs };
    return mk_macro(*g_equation, 2, args);
}

bool is_decreasing(expr const & e) { return is_macro(e) && macro_def(e) == *g_decreasing; }
expr const & decreasing_app(expr const & e) { lean_assert(is_decreasing(e)); return macro_arg(e, 0); }
expr const & decreasing_proof(expr const & e) { lean_assert(is_decreasing(e)); return macro_arg(e, 1); }
expr mk_decreasing(expr const & t, expr const & H) {
    expr args[2] = { t, H };
    return mk_macro(*g_decreasing, 2, args);
}

bool is_equations(expr const & e) { return is_macro(e) && macro_def(e).get_name() == *g_equations_name; }
bool is_wf_equations_core(expr const & e) {
    lean_assert(is_equations(e));
    return macro_num_args(e) >= 3 && !is_lambda_equation(macro_arg(e, macro_num_args(e) - 1));
}
bool is_wf_equations(expr const & e) { return is_equations(e) && is_wf_equations_core(e); }
unsigned equations_size(expr const & e) {
    lean_assert(is_equations(e));
    if (is_wf_equations_core(e))
        return macro_num_args(e) - 2;
    else
        return macro_num_args(e);
}
unsigned equations_num_fns(expr const & e) {
    lean_assert(is_equations(e));
    return static_cast<equations_macro_cell const*>(macro_def(e).raw())->get_num_fns();
}
expr const & equations_wf_proof(expr const & e) {
    lean_assert(is_wf_equations(e));
    return macro_arg(e, macro_num_args(e) - 1);
}
expr const & equations_wf_rel(expr const & e) {
    lean_assert(is_wf_equations(e));
    return macro_arg(e, macro_num_args(e) - 2);
}
void to_equations(expr const & e, buffer<expr> & eqns) {
    lean_assert(is_equations(e));
    unsigned sz = equations_size(e);
    for (unsigned i = 0; i < sz; i++)
        eqns.push_back(macro_arg(e, i));
}
expr mk_equations(unsigned num_fns, unsigned num_eqs, expr const * eqs) {
    lean_assert(num_fns > 0);
    lean_assert(num_eqs > 0);
    lean_assert(std::all_of(eqs, eqs+num_eqs, is_lambda_equation));
    macro_definition def(new equations_macro_cell(num_fns));
    return mk_macro(def, num_eqs, eqs);
}
expr mk_equations(unsigned num_fns, unsigned num_eqs, expr const * eqs, expr const & R, expr const & Hwf) {
    lean_assert(num_fns > 0);
    lean_assert(num_eqs > 0);
    lean_assert(std::all_of(eqs, eqs+num_eqs, is_lambda_equation));
    buffer<expr> args;
    args.append(num_eqs, eqs);
    args.push_back(R);
    args.push_back(Hwf);
    macro_definition def(new equations_macro_cell(num_fns));
    return mk_macro(def, args.size(), args.data());
}

expr update_equations(expr const & eqns, buffer<expr> const & new_eqs) {
    lean_assert(is_equations(eqns));
    lean_assert(!new_eqs.empty());
    if (is_wf_equations(eqns)) {
        return mk_equations(equations_num_fns(eqns), new_eqs.size(), new_eqs.data(),
                            equations_wf_rel(eqns), equations_wf_proof(eqns));
    } else {
        return mk_equations(equations_num_fns(eqns), new_eqs.size(), new_eqs.data());
    }
}

expr mk_inaccessible(expr const & e) { return mk_annotation(*g_inaccessible_name, e); }
bool is_inaccessible(expr const & e) { return is_annotation(e, *g_inaccessible_name); }

void initialize_equations() {
    g_equations_name    = new name("equations");
    g_equation_name     = new name("equation");
    g_decreasing_name   = new name("decreasing");
    g_inaccessible_name = new name("innaccessible");
    g_equation          = new macro_definition(new equation_macro_cell());
    g_decreasing        = new macro_definition(new decreasing_macro_cell());
    g_equations_opcode  = new std::string("Eqns");
    g_equation_opcode   = new std::string("Eqn");
    g_decreasing_opcode = new std::string("Decr");
    register_annotation(*g_inaccessible_name);
    register_macro_deserializer(*g_equations_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    unsigned num_fns;
                                    d >> num_fns;
                                    if (num == 0 || num_fns == 0)
                                        throw corrupted_stream_exception();
                                    if (!is_lambda_equation(args[num-1])) {
                                        if (num <= 2)
                                            throw corrupted_stream_exception();
                                        return mk_equations(num_fns, num-2, args, args[num-2], args[num-1]);
                                    } else {
                                        return mk_equations(num_fns, num, args);
                                    }
                                });
    register_macro_deserializer(*g_equation_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_equation(args[0], args[1]);
                                });
    register_macro_deserializer(*g_decreasing_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_decreasing(args[0], args[1]);
                                });
}

void finalize_equations() {
    delete g_equation_opcode;
    delete g_equations_opcode;
    delete g_decreasing_opcode;
    delete g_equation;
    delete g_decreasing;
    delete g_equations_name;
    delete g_equation_name;
    delete g_decreasing_name;
    delete g_inaccessible_name;
}

class equation_compiler_fn {
    type_checker &   m_tc;
    io_state const & m_ios;
    expr             m_meta;
    expr             m_meta_type;
    bool             m_relax;

    environment const & env() const { return m_tc.env(); }

    struct validate_exception {
        expr m_expr;
        validate_exception(expr const & e):m_expr(e) {}
    };

    bool is_constructor(expr const & e) const {
        return is_constant(e) && inductive::is_intro_rule(env(), const_name(e));
    }

    name mk_fresh_name() { return m_tc.mk_fresh_name(); }

    expr whnf(expr const & e) { return m_tc.whnf(e).first; }
    bool is_def_eq(expr const & e1, expr const & e2) { return m_tc.is_def_eq(e1, e2).first; }

    [[ noreturn ]] static void throw_error(char const * msg, expr const & src) { throw_generic_exception(msg, src); }
    [[ noreturn ]] static void throw_error(expr const & src, pp_fn const & fn) { throw_generic_exception(src, fn); }

    void check_limitations(expr const & eqns) const {
        if (is_wf_equations(eqns) && equations_num_fns(eqns) != 1)
            throw_error("mutually recursive equations do not support well-founded recursion yet", eqns);
    }

    // Return true iff the lhs of eq is of the form (fn ...)
    static bool is_equation_of(expr const & eq, name const & fn) {
        expr const * it = &eq;
        while (is_lambda(*it))
            it = &binding_body(*it);
        lean_assert(is_equation(*it));
        return mlocal_name(get_app_fn(equation_lhs(*it))) == fn;
    }

    expr to_telescope(expr const & e, buffer<expr> & tele) {
        name_generator ngen = m_tc.mk_ngen();
        return ::lean::to_telescope(ngen, e, tele, optional<binder_info>());
    }

    expr fun_to_telescope(expr const & e, buffer<expr> & tele) {
        name_generator ngen = m_tc.mk_ngen();
        return ::lean::fun_to_telescope(ngen, e, tele, optional<binder_info>());
    }

    // --------------------------------
    // Pattern validation/normalization
    // --------------------------------

    expr validate_lhs_arg(expr arg) {
        if (is_inaccessible(arg))
            return arg;
        if (is_local(arg))
            return arg;
        expr new_arg = whnf(arg);
        if (is_local(new_arg))
            return new_arg;
        buffer<expr> arg_args;
        expr const & fn = get_app_args(new_arg, arg_args);
        if (!is_constructor(fn))
            throw validate_exception(arg);
        for (expr & arg_arg : arg_args)
            arg_arg = validate_lhs_arg(arg_arg);
        return mk_app(fn, arg_args);
    }

    expr validate_lhs(expr const & lhs) {
        buffer<expr> args;
        expr fn = get_app_args(lhs, args);
        for (expr & arg : args) {
            try {
                arg = validate_lhs_arg(arg);
            } catch (validate_exception & ex) {
                expr problem_expr = ex.m_expr;
                throw_error(lhs, [=](formatter const & fmt) {
                        format r("invalid argument, it is not a constructor, variable, "
                                 "nor it is marked as an inaccessible pattern");
                        r += pp_indent_expr(fmt, problem_expr);
                        r += compose(line(), format("in the following equation left-hand-side"));
                        r += pp_indent_expr(fmt, lhs);
                        return r;
                    });
            }
        }
        return mk_app(fn, args);
    }

    expr validate_patterns_core(expr eq) {
        buffer<expr> args;
        eq = fun_to_telescope(eq, args);
        lean_assert(is_equation(eq));
        expr new_lhs = validate_lhs(equation_lhs(eq));
        return Fun(args, mk_equation(new_lhs, equation_rhs(eq)));
    }

    expr validate_patterns(expr const & eqns) {
        lean_assert(is_equations(eqns));
        buffer<expr> eqs;
        buffer<expr> new_eqs;
        to_equations(eqns, eqs);
        for (expr const & eq : eqs) {
            new_eqs.push_back(validate_patterns_core(eq));
        }
        return update_equations(eqns, new_eqs);
    }

    // --------------------------------
    // Structural recursion
    // --------------------------------

    // Return true iff \c s is structurally smaller than \c t OR equal to \c t
    bool is_le(expr const & s, expr const & t) {
        return is_def_eq(s, t) || is_lt(s, t);
    }

    // Return true iff \c s is structurally smaller than \c t
    bool is_lt(expr s, expr const & t) {
        s = whnf(s);
        if (is_app(s)) {
            expr const & s_fn = get_app_fn(s);
            if (!is_constructor(s_fn))
                return is_lt(s_fn, t); // f < t ==> s := f a_1 ... a_n < t
        }
        buffer<expr> t_args;
        expr const & t_fn = get_app_args(t, t_args);
        if (!is_constructor(t_fn))
            return false;
        return std::any_of(t_args.begin(), t_args.end(), [&](expr const & t_arg) { return is_le(s, t_arg); });
    }

    // Return true if the arg_idx-th argument of this equation structurally decreases in every recursive call.
    bool is_decreasing_eq(expr eq, unsigned arg_idx) {
        buffer<expr> eq_ctx;
        eq = fun_to_telescope(eq, eq_ctx);
        expr const & lhs = equation_lhs(eq);
        buffer<expr> lhs_args;
        expr const & fn  = get_app_args(lhs, lhs_args);
        if (arg_idx >= lhs_args.size())
            return false;
        name const & fn_name = mlocal_name(fn);
        bool is_ok = true;
        for_each(equation_rhs(eq),
                 [&](expr const & e, unsigned) {
                     if (!is_ok) return false;
                     expr const & fn = get_app_fn(e);
                     if (is_local(fn) && mlocal_name(fn) == fn_name) {
                         buffer<expr> rhs_args;
                         get_app_args(e, rhs_args);
                         if (arg_idx >= rhs_args.size())
                             return false;
                         if (!is_lt(rhs_args[arg_idx], lhs_args[arg_idx]))
                             is_ok = false;
                     }
                     return true;
                 });
        return is_ok;
    }

    bool is_valid_rec_arg(buffer<expr> const & args, unsigned idx, unsigned nm) {
        expr const & arg = args[idx];
        expr arg_type    = whnf(mlocal_type(arg));
        expr arg_type_fn = get_app_fn(arg_type);
        if (!is_constant(arg_type_fn))
            return false;
        if (auto it = inductive::is_inductive_decl(env(), const_name(arg_type_fn))) {
            if (length(std::get<2>(*it)) != nm)
                return false; // number of mutually recursive functions is different from number of mutually recursive types
            if (!env().find(name(const_name(arg_type_fn), "brec_on")))
                return false; // recursive datatype does not have a brec_on recursor
            // must check dependencies
            return true;
        } else {
            return false;
        }
    }

    // Create a new proof_state by using brec_on to justify recursive calls
    proof_state apply_brec_on(expr const & eqns, proof_state const & ps) {
        unsigned num_fns = equations_num_fns(eqns);
        buffer<expr> eqs;
        to_equations(eqns, eqs);
        buffer<expr> fns;
        buffer<name> fn_names;
        bool first = true;
        for (expr & eq : eqs) {
            if (first) {
                for (unsigned i = 0; i < num_fns; i++) {
                    expr fn = mk_local(mk_fresh_name(), binding_name(eq), binding_domain(eq), binder_info());
                    fns.push_back(fn);
                    fn_names.push_back(mlocal_name(fn));
                    eq      = instantiate(binding_body(eq), fn);
                }
            } else {
                for (expr const & fn : fns)
                    eq = instantiate(binding_body(eq), fn);
            }
            first = false;
        }

        // Find an argument of the first equation that is structurally decreasing in all equations
        expr fn1 = fns[0];
        expr fn1_type = mlocal_type(fn1);
        buffer<expr> args1;
        to_telescope(fn1_type, args1);
        for (unsigned i = 0; i < args1.size(); i++) {
            if (!is_valid_rec_arg(args1, i, num_fns))
                continue;
            if (std::all_of(eqs.begin(), eqs.end(), [&](expr const & eq) {
                        return !is_equation_of(eq, mlocal_name(fn1)) || is_decreasing_eq(eq, i);
                    })) {
                std::cout << "ARG: " << i << " decreases at " << local_pp_name(fn1) << "\n";
            }
        }

        // TODO: check non-recursive case

        return ps;
    }

public:
    equation_compiler_fn(type_checker & tc, io_state const & ios, expr const & meta, expr const & meta_type, bool relax):
        m_tc(tc), m_ios(ios), m_meta(meta), m_meta_type(meta_type), m_relax(relax) {
    }

    expr operator()(expr eqns) {
        check_limitations(eqns);
        proof_state ps = to_proof_state(m_meta, m_meta_type, m_tc.mk_ngen(), m_relax);
        eqns = validate_patterns(eqns);
        if (is_wf_equations(eqns)) {
            // TODO(Leo)
        } else {
            ps = apply_brec_on(eqns, ps);
        }

        regular(env(), m_ios) << "Equations:\n" << eqns << "\n";
        regular(env(), m_ios) << ps.pp(env(), m_ios) << "\n\n";
        substitution s = ps.get_subst();
        return s.instantiate_all(m_meta);
    }
};

expr compile_equations(type_checker & tc, io_state const & ios, expr const & eqns,
                       expr const & meta, expr const & meta_type, bool relax) {
    return equation_compiler_fn(tc, ios, meta, meta_type, relax)(eqns);
}
}
