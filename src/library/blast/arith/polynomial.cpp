/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <algorithm>
#include <vector>
#include "library/blast/arith/polynomial.h"
#include "library/blast/trace.h"

namespace lean {
namespace blast {

/* atoms */
bool operator==(atom const & a1, atom const & a2) {
    return a1.get_power() == a2.get_power() && a1.get_expr() == a2.get_expr();
}

/* add */
void polynomial::add(polynomial p) {
    m_monomials.insert(m_monomials.end(), p.get_monomials().begin(), p.get_monomials().end());
    m_offset += p.m_offset;
}

/* mul */
void polynomial::mul(polynomial p) {
    std::vector<monomial> new_monomials;
    for (monomial m1 : m_monomials) {
        mpq new_coefficient = m1.get_coefficient(); new_coefficient *= p.get_offset();
        if (!new_coefficient.is_zero()) new_monomials.emplace_back(new_coefficient, m1.get_atoms());
        for (monomial m2 : p.m_monomials) {
            mpq new_coefficient = m1.get_coefficient(); new_coefficient *= m2.get_coefficient();
            std::vector<atom> new_atoms;
            new_atoms.insert(new_atoms.end(), m1.get_atoms().begin(), m1.get_atoms().end());
            new_atoms.insert(new_atoms.end(), m2.get_atoms().begin(), m2.get_atoms().end());
            new_monomials.emplace_back(new_coefficient, new_atoms);
        }
    }
    for (monomial m2 : p.m_monomials) {
        mpq new_coefficient{m2.get_coefficient()}; new_coefficient *= get_offset();
        if (!new_coefficient.is_zero()) new_monomials.emplace_back(new_coefficient, m2.get_atoms());
    }
    m_offset *= p.get_offset();
    m_monomials = new_monomials;
}

/* fuse */
void monomial::fuse_atoms() {
    std::sort(m_atoms.begin(), m_atoms.end(), atom_fuse_lt());
    std::vector<atom> new_atoms;
    unsigned i = 0;
    while (i < m_atoms.size()) {
        atom a = m_atoms[i];
        i++;
        while (i < m_atoms.size() && m_atoms[i].get_expr() == m_atoms[i-1].get_expr()) {
            a.add_power(m_atoms[i].get_power());
            i++;
        }
        if (a.get_power() != 0) new_atoms.push_back(a);
    }
    m_atoms = new_atoms;
}

void polynomial::fuse_monomials() {
    for (monomial & m : m_monomials) m.fuse_atoms();
    std::sort(m_monomials.begin(), m_monomials.end(), monomial_fuse_lt());
    std::vector<monomial> new_monomials;
    unsigned i = 0;
    while (i < m_monomials.size()) {
        monomial m = m_monomials[i];
        if (m.get_atoms().empty()) { i++; m_offset += m.get_coefficient(); continue; }
        i++;
        while (i < m_monomials.size() && m_monomials[i].get_atoms() == m_monomials[i-1].get_atoms()) {
            m.add_coefficient(m_monomials[i].get_coefficient());
            i++;
        }
        if (m.get_coefficient() != 0) new_monomials.push_back(m);
    }
    m_monomials = new_monomials;
}

/* Printing */
// TODO(dhs): use [io_state_stream] so that we can pretty-print
// issue: printing mpqs
std::ostream & operator<<(std::ostream & out, atom const & a) {
    out << a.get_expr() << "::" << a.get_power();
    return out;
}

std::ostream & operator<<(std::ostream & out, monomial const & _m) {
    monomial m = _m;
    out << "(" << m.get_coefficient() << ", ";
    bool first = true;
    for (atom const & a : m.get_atoms()) {
        if (!first) out << " * ";
        first = false;
        out << a;
    }
    out << ")";
    return out;
}

std::ostream & operator<<(std::ostream & out, polynomial const & _p) {
    polynomial p = _p;
    out << "{" << p.get_offset();
    for (monomial const & m : p.get_monomials()) {
        out << ", " << m;
    }
    out << "}";
    return out;
}
}}
