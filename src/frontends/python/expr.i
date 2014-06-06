%module expr
%{
#include "kernel/expr.h"
#include "util/name.h"
using namespace lean;

%}
//name
// =====================================
// Class definition
class name {
public:
    name(char const * name);
    ~name();
};


//expr
// ======================================
// Class definition
class expr {
public:
    expr();
    expr(expr && s);
    ~expr();

    friend void swap(expr & a, expr & b);

    expr_kind kind() const;
    bool has_metavar() const;

    friend bool is_eqp(expr const & a, expr const & b);
    // Overloaded operator() can be used to create applications
    expr operator()(expr const & a1) const;
    expr operator()(expr const & a1, expr const & a2) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6, expr const & a7) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6, expr const & a7, expr const & a8) const;
};

// =======================================
// Testers
bool is_var(expr const & e);
bool is_constant(expr const & e);
bool is_value(expr const & e);
bool is_dep_pair(expr const & e);
bool is_proj(expr const & e);
bool is_app(expr const & e);
bool is_lambda(expr const & e);
bool is_pi(expr const & e);
bool is_arrow(expr const & e);
bool is_cartesian(expr const & e);
bool is_sigma(expr const & e);
bool is_type(expr const & e);
bool is_let(expr const & e);
bool is_heq(expr const & e);
bool is_metavar(expr const & e);
bool is_abstraction(expr const & e);
// =======================================

// =======================================
// Constructors
expr mk_var(unsigned idx);
expr Var(unsigned idx);
expr mk_constant(name const & n, optional<expr> const & t);
expr mk_constant(name const & n, expr const & t);
expr mk_constant(name const & n);
expr Const(name const & n);
expr mk_value(value & v);
expr to_expr(value & v);
expr mk_pair(expr const & f, expr const & s, expr const & t);
expr mk_proj(bool f, expr const & e);
expr mk_proj1(expr const & e);
expr mk_proj2(expr const & e);
expr mk_app(unsigned num_args, expr const * args);
expr mk_lambda(name const & n, expr const & t, expr const & e);
expr mk_pi(name const & n, expr const & t, expr const & e);
expr mk_sigma(name const & n, expr const & t, expr const & e);
bool is_default_arrow_var_name(name const & n);
expr mk_arrow(expr const & t, expr const & e);
expr mk_cartesian_product(expr const & t, expr const & e);
expr mk_let(name const & n, expr const & t, expr const & v, expr const & e);
expr mk_let(name const & n, expr const & v, expr const & e);
expr mk_type(level const & l);
expr mk_type();
expr Type(level const & l);
expr Type();
expr mk_heq(expr const & lhs, expr const & rhs);
expr mk_metavar(name const & n, local_context const & ctx = local_context());
