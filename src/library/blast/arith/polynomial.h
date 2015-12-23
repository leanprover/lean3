/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <memory>
#include <vector>
#include "kernel/expr.h"
#include "library/expr_lt.h"
#include "util/rb_map.h"
#include "util/numerics/mpq.h"

namespace lean {
namespace blast {

class atom {
    expr                    m_e;
    int                     m_pow;
public:
    atom(expr const & e, int pow): m_e(e), m_pow(pow) {}
    atom(atom const & a): m_e(a.m_e), m_pow(a.m_pow) {}
    expr const & get_expr() const { return m_e; }
    int get_power() const { return m_pow; }
    void add_power(int pow) { m_pow += pow; }
};

bool operator==(atom const & a1, atom const & a2);
inline bool operator!=(atom const & a1, atom const & a2) { return !(a1 == a2); }

struct atom_fuse_lt {
    bool operator()(atom const & a1, atom const & a2) const {
        // TODO(dhs): confirm that we do not need to make this a total order
        // (only used for fusing right now)
        return expr_quick_lt()(a1.get_expr(), a2.get_expr());
    }
};

struct atoms_quick_cmp {
    int operator()(std::vector<atom> const & as1, std::vector<atom> const & as2) const {
        int size_cmp = unsigned_cmp()(as1.size(), as2.size());
        if (size_cmp) return size_cmp;
        for (unsigned i = 0; i < as1.size(); i++) {
            int expr_cmp = expr_quick_cmp()(as1[i].get_expr(), as2[i].get_expr());
            if (expr_cmp) return expr_cmp;
            int power_cmp = unsigned_cmp()(as1[i].get_power(), as2[i].get_power());
            if (power_cmp) return power_cmp;
        }
        return 0;
    }
};

// TODO(dhs): encapsulate a vector of atoms as a type, so we make cheap copies and use them
// as keys in a map
class monomial {
    mpq                      m_coefficient;
    std::vector<atom>        m_atoms;
public:
    monomial(mpq const & coefficient, std::vector<atom> const & atoms):
        m_coefficient(coefficient), m_atoms(atoms) {}
    monomial(monomial const & m): m_coefficient(m.m_coefficient), m_atoms(m.m_atoms) {}

    mpq const & get_coefficient() const { return m_coefficient; }
    std::vector<atom> const & get_atoms() const { return m_atoms; }
    void add_coefficient(mpq const & coefficient) { m_coefficient += coefficient; }
    void fuse_atoms();
};

struct monomial_fuse_lt {
    /* Only looks at the atoms. Is used for fusing monomials in a polynomial. */
    bool operator()(monomial const & m1, monomial const & m2) {
        return atoms_quick_cmp()(m1.get_atoms(), m2.get_atoms()) < 0;
    }
};

class polynomial {
    mpq                      m_offset{0};
    std::vector<monomial>    m_monomials;
 public:
    polynomial() {}
    polynomial(mpq const & offset, bool inv, bool neg): m_offset(offset) {
        if (inv && !m_offset.is_zero()) m_offset.inv();
        if (neg) m_offset.neg();
    }
    polynomial(expr const & e, bool inv, bool neg) {
        std::vector<atom> atoms;
        atoms.emplace_back(e, inv ? -1 : 1);
        mpq coefficient(1);
        if (neg) coefficient.neg();
        m_monomials.emplace_back(coefficient, atoms);
    }
    polynomial(polynomial const & p): m_offset(p.m_offset), m_monomials(p.m_monomials) {}

    mpq const & get_offset() const { return m_offset; }
    std::vector<monomial> const & get_monomials() const { return m_monomials; }
    void add(polynomial p);
    void mul(polynomial p);
    void fuse_monomials();
};

/* Note: these expressions are not necessarily normalized.
   There may be extraneous 0s and 1s. This would be easy to address. */
expr atom_to_expr(atom const & a, expr const & type);
expr monomial_to_expr(monomial const & m, expr const & type);
expr polynomial_to_expr(polynomial const & p, expr const & type);

std::ostream & operator<<(std::ostream & out, atom const & a);
std::ostream & operator<<(std::ostream & out, monomial const & m);
std::ostream & operator<<(std::ostream & out, polynomial const & p);

}}
