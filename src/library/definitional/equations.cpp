/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "util/list_fn.h"
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
    buffer<expr>     m_ctx; // global context
    buffer<expr>     m_fns; // functions being defined

    environment const & env() const { return m_tc.env(); }
    io_state const & ios() const { return m_ios; }
    io_state_stream out() const { return regular(env(), ios()); }
    name mk_fresh_name() { return m_tc.mk_fresh_name(); }
    expr whnf(expr const & e) { return m_tc.whnf(e).first; }
    bool is_def_eq(expr const & e1, expr const & e2) { return m_tc.is_def_eq(e1, e2).first; }

    optional<name> is_constructor(expr const & e) const {
        if (!is_constant(e))
            return optional<name>();
        return inductive::is_intro_rule(env(), const_name(e));
    }

    expr to_telescope(expr const & e, buffer<expr> & tele) {
        name_generator ngen = m_tc.mk_ngen();
        return ::lean::to_telescope(ngen, e, tele, optional<binder_info>());
    }

    expr fun_to_telescope(expr const & e, buffer<expr> & tele) {
        name_generator ngen = m_tc.mk_ngen();
        return ::lean::fun_to_telescope(ngen, e, tele, optional<binder_info>());
    }

    [[ noreturn ]] static void throw_error(char const * msg, expr const & src) { throw_generic_exception(msg, src); }
    [[ noreturn ]] static void throw_error(expr const & src, pp_fn const & fn) { throw_generic_exception(src, fn); }
    [[ noreturn ]] void throw_error(sstream const & ss) { throw_generic_exception(ss, m_meta); }

    void check_limitations(expr const & eqns) const {
        if (is_wf_equations(eqns) && equations_num_fns(eqns) != 1)
            throw_error("mutually recursive equations do not support well-founded recursion yet", eqns);
    }

    struct eqn {
        // The local context for an equation is a list of all
        // local constants occurring in m_patterns and m_rhs
        // which are not in the global context m_ctx or the
        // functions being defined m_fns
        list<expr> m_local_ctx;
        list<expr> m_patterns; // patterns to be processed
        expr       m_rhs;      // right-hand-side
        eqn(list<expr> const & c, list<expr> const & p, expr const & r):
            m_local_ctx(c), m_patterns(p), m_rhs(r) {}
    };

    // Data-structure used to store for compiling pattern matching.
    // We create a program object for each function being defined
    struct program {
        list<expr> m_var_stack; // variables that must be matched with the patterns
        list<eqn>  m_eqns;      // equations
        // The goal of the compiler is to process all variables in m_var_stack
        program(list<expr> const & s, list<eqn> const & e):m_var_stack(s), m_eqns(e) {}
        program() {}
    };

    // For debugging purposes
    template<typename T>
    static bool contains_local(T const & locals, expr const & l) {
        return std::any_of(locals.begin(), locals.end(),
                           [&](expr const & l1) { return mlocal_name(l1) == mlocal_name(l); });
    }

    // For debugging purposes: checks whether all local constants occurring in \c e
    // are in local_ctx or m_ctx
    bool check_ctx(expr const & e, list<expr> const & local_ctx) const {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_local(e) &&
                    !(contains_local(local_ctx, e) ||
                      contains_local(m_ctx, e) ||
                      contains_local(m_fns, e))) {
                    lean_unreachable();
                    return false;
                }
                return true;
            });
        return true;
    }

    // For debugging purposes: check if the program is well-formed
    bool check_program(program const & s) const {
        unsigned sz = length(s.m_var_stack);
        for (eqn const & e : s.m_eqns) {
            // the number of patterns in each equation is equal to the variable stack size
            if (length(e.m_patterns) != sz) {
                lean_unreachable();
                return false;
            }
            check_ctx(e.m_rhs, e.m_local_ctx);
            for (expr const & p : e.m_patterns)
                check_ctx(p, e.m_local_ctx);
        }
        return true;
    }

    // Initialize m_fns (the vector of functions to be compiled)
    void initialize_fns(expr const & eqns) {
        lean_assert(is_equations(eqns));
        unsigned num_fns = equations_num_fns(eqns);
        buffer<expr> eqs;
        to_equations(eqns, eqs);
        expr eq = eqs[0];
        for (unsigned i = 0; i < num_fns; i++) {
            expr fn = mk_local(mk_fresh_name(), binding_name(eq), binding_domain(eq), binder_info());
            m_fns.push_back(fn);
            eq      = instantiate(binding_body(eq), fn);
        }
    }

    // Initialize the variable stack for each function that needs
    // to be compiled.
    // This method assumes m_fns has been already initialized.
    // This method also initialized the buffer prg, but the eqns
    // field of each program is not initialized by it.
    void initialize_var_stack(buffer<program> & prgs) {
        lean_assert(!m_fns.empty());
        lean_assert(prgs.empty());
        for (expr const & fn : m_fns) {
            buffer<expr> args;
            to_telescope(mlocal_type(fn), args);
            program p;
            p.m_var_stack = to_list(args);
            prgs.push_back(p);
        }
    }

    struct validate_exception {
        expr m_expr;
        validate_exception(expr const & e):m_expr(e) {}
    };

    // Validate/normalize the given pattern.
    // It stores in reachable_vars any variable that does not occur
    // in inaccessible terms.
    expr validate_pattern(expr pat, name_set & reachable_vars) {
        if (is_inaccessible(pat))
            return pat;
        if (is_local(pat)) {
            reachable_vars.insert(mlocal_name(pat));
            return pat;
        }
        expr new_pat = whnf(pat);
        if (is_local(new_pat)) {
            reachable_vars.insert(mlocal_name(new_pat));
            return new_pat;
        }
        buffer<expr> pat_args;
        expr const & fn = get_app_args(new_pat, pat_args);
        if (auto in = is_constructor(fn)) {
            unsigned num_params = *inductive::get_num_params(env(), *in);
            for (unsigned i = num_params; i < pat_args.size(); i++)
                pat_args[i] = validate_pattern(pat_args[i], reachable_vars);
            return mk_app(fn, pat_args);
        } else {
            throw validate_exception(pat);
        }
    }

    // Validate/normalize the patterns associated with the given lhs.
    // The lhs is only used to report errors.
    // It stores in reachable_vars any variable that does not occur
    // in inaccessible terms.
    void validate_patterns(expr const & lhs, buffer<expr> & patterns, name_set & reachable_vars) {
        for (expr & pat : patterns) {
            try {
                pat = validate_pattern(pat, reachable_vars);
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
    }

    // Create initial program state for each function being defined.
    void initialize(expr const & eqns, buffer<program> & prg) {
        lean_assert(is_equations(eqns));
        initialize_fns(eqns);
        initialize_var_stack(prg);
        buffer<expr> eqs;
        to_equations(eqns, eqs);
        buffer<buffer<eqn>> res_eqns;
        res_eqns.resize(m_fns.size());
        for (expr eq : eqs) {
            for (expr const & fn : m_fns)
                eq = instantiate(binding_body(eq), fn);
            buffer<expr> local_ctx;
            eq = fun_to_telescope(eq, local_ctx);
            expr const & lhs = equation_lhs(eq);
            expr const & rhs = equation_rhs(eq);
            buffer<expr> patterns;
            expr const & fn  = get_app_args(lhs, patterns);
            name_set reachable_vars;
            validate_patterns(lhs, patterns, reachable_vars);
            for (expr const & v : local_ctx) {
                // every variable in the local_ctx must be "reachable".
                if (!reachable_vars.contains(mlocal_name(v))) {
                    throw_error(lhs, [=](formatter const & fmt) {
                            format r("invalid equation left-hand-side, variable '");
                            r += format(local_pp_name(v));
                            r += format("' only occurs in inaccessible terms in the following equation left-hand-side");
                            r += pp_indent_expr(fmt, lhs);
                            return r;
                        });
                }
            }
            for (unsigned i = 0; i < m_fns.size(); i++) {
                if (mlocal_name(fn) == mlocal_name(m_fns[i])) {
                    if (patterns.size() != length(prg[i].m_var_stack))
                        throw_error("ill-formed equation, number of provided arguments does not match function type", eq);
                    res_eqns[i].push_back(eqn(to_list(local_ctx), to_list(patterns), rhs));
                }
            }
        }
        for (unsigned i = 0; i < m_fns.size(); i++) {
            prg[i].m_eqns = to_list(res_eqns[i]);
            lean_assert(check_program(prg[i]));
        }
    }

    // For debugging purposes: display the context at m_ios
    template<typename Ctx>
    void display_ctx(Ctx const & ctx) const {
        bool first = true;
        for (expr const & e : ctx) {
            out() << (first ? "" : ", ") << local_pp_name(e) << " : " << mlocal_type(e);
            first = false;
        }
    }

    // For debugging purposes: dump prg in m_ios
    void display(program const & prg) const {
        display_ctx(prg.m_var_stack);
        out() << "\n";
        for (eqn const & e : prg.m_eqns) {
            out() << "> ";
            display_ctx(e.m_local_ctx);
            out() << " |-";
            for (expr const & p : e.m_patterns) {
                if (is_atomic(p))
                    out() << " " << p;
                else
                    out() << " (" << p << ")";
            }
            out() << " := " << e.m_rhs << "\n";
        }
    }

    // Return true iff the next pattern in all equations is a variable or an inaccessible term
    bool is_variable_transition(program const & p) const {
        for (eqn const & e : p.m_eqns) {
            lean_assert(e.m_patterns);
            if (!is_local(head(e.m_patterns)) && !is_inaccessible(head(e.m_patterns)))
                return false;
        }
        return true;
    }

    // Return true iff the next pattern in all equations is a constructor
    bool is_constructor_transition(program const & p) const {
        for (eqn const & e : p.m_eqns) {
            lean_assert(e.m_patterns);
            if (!is_constructor(get_app_fn(head(e.m_patterns))))
                return false;
        }
        return true;
    }

    // Return true iff the next pattern of every equation is a constructor or variable,
    // and there are at least one equation where it is a variable and another where it is a
    // constructor.
    bool is_complete_transition(program const & p) const {
        bool has_variable    = false;
        bool has_constructor = false;
        for (eqn const & e : p.m_eqns) {
            lean_assert(e.m_patterns);
            expr const & p = head(e.m_patterns);
            if (is_local(p))
                has_variable = true;
            else if (is_constructor(get_app_fn(p)))
                has_constructor = true;
            else
                return false;
        }
        return has_variable && has_constructor;
    }

    // Remove variable from local context
    static list<expr> remove(list<expr> const & local_ctx, expr const & l) {
        lean_assert(local_ctx);
        if (mlocal_name(head(local_ctx)) == mlocal_name(l))
            return tail(local_ctx);
        else
            return cons(head(local_ctx), remove(tail(local_ctx), l));
    }

    // Replace local constant \c from with \c to in the expression \c e.
    static expr replace(expr const & e, expr const & from, expr const & to) {
        return instantiate(abstract_local(e, from), to);
    }

    expr compile_variable(program const & p, unsigned i) {
        // The next pattern of every equation is a variable (or inaccessible term).
        // Thus, we just rename them with the variable on
        // the top of the variable stack.
        // Remark: if the pattern is an inaccessible term, we just ignore it.
        expr x = head(p.m_var_stack);
        auto new_stack = tail(p.m_var_stack);
        buffer<eqn> new_eqs;
        for (eqn const & e : p.m_eqns) {
            expr p = head(e.m_patterns);
            if (is_inaccessible(p)) {
                new_eqs.emplace_back(e.m_local_ctx, tail(e.m_patterns), e.m_rhs);
            } else {
                lean_assert(is_local(p));
                auto new_local_ctx = cons(x, map(remove(e.m_local_ctx, p), [&](expr const & l) { return replace(l, p, x); }));
                auto new_patterns  = map(tail(e.m_patterns), [&](expr const & p2) { return replace(p2, p, x); });
                auto new_rhs       = replace(e.m_rhs, p, x);
                new_eqs.emplace_back(new_local_ctx, new_patterns, new_rhs);
            }
        }
        return compile_core(program(new_stack, to_list(new_eqs)), i);
    }

    expr compile_constructor(program const & p, unsigned i) {
        // The next pattern of every equation is a constructor.
        // Thus, we case-split the variable on the top of variable stack.

        // TODO(Leo)
        return expr();
    }

    expr compile_complete(program const & p, unsigned i) {
        // The next pattern of every equation is a constructor or variable.
        // We split the equations where the next pattern is a variable into cases.
        // That is, we are reducing this case to the compile_constructor case.

        // TODO(Leo)
        return expr();
    }

    expr compile_core(program const & p, unsigned i) {
        lean_assert(check_program(p));
        if (p.m_var_stack) {
            if (is_variable_transition(p)) {
                return compile_variable(p, i);
            } else if (is_constructor_transition(p)) {
                return compile_constructor(p, i);
            } else if (is_complete_transition(p)) {
                return compile_complete(p, i);
            } else {
                // In some equations the next pattern is an inaccessible term,
                // and in others it is a constructor.
                throw_error(sstream() << "invalid recursive equations for '" << local_pp_name(m_fns[i])
                            << "', inconsistent use of inaccessible term annotation, "
                            << "in some equations a pattern is a constructor, and in another it is an inaccessible term");
            }
        } else {
            // variable stack is empty
            return head(p.m_eqns).m_rhs;
        }
    }

    expr compile(program const & p, unsigned i) {
        buffer<expr> vars;
        to_buffer(p.m_var_stack, vars);
        expr r = compile_core(p, i);
        return Fun(vars, r);
    }

public:
    equation_compiler_fn(type_checker & tc, io_state const & ios, expr const & meta, expr const & meta_type, bool relax):
        m_tc(tc), m_ios(ios), m_meta(meta), m_meta_type(meta_type), m_relax(relax) {
        get_app_args(m_meta, m_ctx);
    }

    expr operator()(expr eqns) {
        check_limitations(eqns);
        out() << "Equations:\n" << eqns << "\n";
        buffer<program> prgs;
        initialize(eqns, prgs);
        unsigned i = 0;
        buffer<expr> rs;
        for (program const & p : prgs) {
            display(p);
            expr r = compile(p, i);
            out() << r << "\n";
            rs.push_back(r);
            i++;
        }
        if (closed(rs[0]))
            return rs[0];
        else
            return m_meta;
    }
};

expr compile_equations(type_checker & tc, io_state const & ios, expr const & eqns,
                       expr const & meta, expr const & meta_type, bool relax) {
    return equation_compiler_fn(tc, ios, meta, meta_type, relax)(eqns);
}
}
