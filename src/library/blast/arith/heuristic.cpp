/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <vector>
#include <algorithm>
#include <memory>
#include "kernel/abstract.h"
#include "util/sexpr/option_declarations.h"
#include "util/numerics/mpq.h"
#include "library/constants.h"
#include "library/blast/proof_expr.h"
#include "library/blast/arith/heuristic.h"
#include "library/blast/arith/num.h"
#include "library/blast/arith/polynomial.h"
#include "library/blast/arith/normalize.h"
#include "library/blast/arith/normalize_poly.h"
#include "library/blast/backward/backward_strategy.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/simplifier/simplifier.h"
#include "library/num.h"

#ifndef LEAN_DEFAULT_HEURISTIC_MAX_STEPS_PER_ACTION
#define LEAN_DEFAULT_HEURISTIC_MAX_STEPS_PER_ACTION 10
#endif

namespace lean {
namespace blast {

/** Globals */
static name * g_heuristic_trace_name           = nullptr;
static name * g_heuristic_max_steps_per_action = nullptr;

static unsigned g_ext_id = 0;

struct arith_heuristic_proof_step_cell : public proof_step_cell {
    list<expr>     m_placeholders;     // placeholders for non-zero proofs

    virtual ~arith_heuristic_proof_step_cell() {}
    arith_heuristic_proof_step_cell(list<expr> const & placeholders):
        m_placeholders(placeholders) {}

    virtual action_result resolve(expr const & pf) const override {
        buffer<expr> proofs;
        for (expr const & placeholder : m_placeholders) {
            optional<expr> pf;
            {
                flet<state> save_state(curr_state(), curr_state());
                curr_state().set_target(mlocal_type(placeholder));
                pf = mk_backward_strategy()();
            }
            if (pf) {
                proofs.push_back(*pf);
            } else {
                lean_trace(*g_heuristic_trace_name, tout() << "failed to prove: " << ppb(mlocal_type(placeholder)) << "\n";);
                return action_result::failed();
            }
        }
        buffer<expr> placeholders;
        to_buffer(m_placeholders, placeholders);
        return action_result::solved(mk_app(Fun(placeholders, pf), proofs));
    }
};

void addmul(mpq & q, mpq const & c, mpq const & x) {
    mpq tmp = c;
    tmp *= x;
    q += tmp;
}

/** Option getters */
unsigned get_heuristic_max_steps_per_action() {
    return ios().get_options().get_unsigned(*g_heuristic_max_steps_per_action, LEAN_DEFAULT_HEURISTIC_MAX_STEPS_PER_ACTION);
}

/* Description:

This module performs linear and some non-linear arithmetic, as described in the paper [HEURISTIC2].

The architecture is as follows:

When the action [assert_heuristic_action(hypothesis_idx)] is called, we
call the [linearizer] to construct a list of polynomial inequalities, of the form

<<
0 < Sum_i [<numeral_i> * <unknown_i>] + <numeral>
>>

where the inequality may or may not be strict.

The linearizer stores a [lazy_proof] in each polynomial inequality that it creates, so that
we can construct a fully formal proof of any contradiction we find.

Then, we proceed to create new polynomial inequalities from old polynomial inequaities, all the while
maintaining a trace of how the new polynomial inequalities can be justified in terms of the old ones.

If we do construct a polynomial inequality of the form [0 < 0, 0 < - <pos>, 0 <= - <pos>], we have
found a contradiction, and we must start to construct a formal proof of this fact.
*/

/** Basic data-structures **/

/* Proof trails */
typedef std::function<expr()> lazy_proof;

class poly;
struct poly_parents {
    // TODO(dhs): switch to reference counting once we have [MK_BLAST_RC()]
    std::shared_ptr<poly> m_p, m_q;
    mpq m_p_scale, m_q_scale;
public:
    poly_parents(poly const & p, poly const & q, mpq const & p_scale, mpq const & q_scale);

    poly const & get_p() const { return *(m_p.get()); }
    poly const & get_q() const { return *(m_q.get()); }
    mpq const & get_p_scale() const { return m_p_scale; }
    mpq const & get_q_scale() const { return m_q_scale; }
};

/* Polynomial inequalities */
enum class poly_kind { Normal, Contradiction, Trivial };

class poly {
    /* Represents a polynomial inequality of the following form:
       0 [<, <=] sum_i (m_monomials[i].coeff * m_monomials[i].unknown) + m_offset
       where the inequality is strict iff `m_strict = true`. */
    expr m_A;
    list<monomial> m_monomials;
    mpq m_offset;
    bool m_strict;

    /* Since we need to prove any resulting "contradicting" polynomial we derive,
       we need to track a justification for each such polynomial.
       There are two cases:
       1. A polynomial inequality may be a "linearization" of an existing hypothesis. In this case
       we store the [hypothesis_idx] of this existing hypothesis. The "linearization"
       module will be responsible for this stage of the proof.
       2. A polynomial inequality may be the result of resolving two existing polynomial inequalities
       together. In this case, we store the two parents along with the scaling factors. To reconstruct
       the proof, we use the "poly_cancel" lemmas. */

    // Poor man's union
    optional<lazy_proof>   m_lazy_proof;    // Case 1
    optional<poly_parents> m_parents;       // Case 2
public:
    poly(poly const & p):
        m_A(p.m_A), m_monomials(p.m_monomials), m_offset(p.m_offset),
        m_strict(p.m_strict), m_lazy_proof(p.m_lazy_proof), m_parents(p.m_parents) {}

    poly(expr const & A, list<monomial> const & monomials, mpq offset, poly_parents const & parents):
        m_A(A), m_monomials(monomials), m_offset(offset),
        m_strict(parents.get_p().is_strict() || parents.get_q().is_strict()), m_parents(parents) {}

    poly(expr const & A, list<monomial> const & monomials, mpq offset, bool strict, lazy_proof const & lproof):
        m_A(A), m_monomials(monomials), m_offset(offset), m_strict(strict), m_lazy_proof(lproof) {}

    list<monomial> const & get_monomials() const { return m_monomials; }
    bool is_strict() const { return m_strict; }
    mpq const & get_offset() const { return m_offset; }

    poly_kind kind() const {
        if (!is_nil(m_monomials)) return poly_kind::Normal;
        else if (is_strict() && m_offset.is_nonpos()) return poly_kind::Contradiction;
        else if (!is_strict() && m_offset.is_neg()) return poly_kind::Contradiction;
        else return poly_kind::Trivial;
    }

    name get_resolve_name() const {
        lean_assert(m_parents);
        if (m_parents->get_p().is_strict() && m_parents->get_q().is_strict()) {
            return get_ordered_arith_resolve_lt_lt_name();
        } else if (m_parents->get_p().is_strict()) {
            return get_ordered_arith_resolve_lt_le_name();
        } else if (m_parents->get_q().is_strict()) {
            return get_ordered_arith_resolve_le_lt_name();
        } else {
            return get_ordered_arith_resolve_le_le_name();
        }
    }

    expr const & get_A() const { return m_A; }

    expr get_clean_thm() const {
        return get_app_builder().mk_lt(m_A, get_app_builder().mk_zero(m_A), mpq_to_expr(m_offset, m_A));
    }

    /* This function returns a proof of the polynomial inequality, except it does not
       take into account the cancellations at each resolution step, hence the name
       [get_proof_messy()]. We have the following proof:

       original_hypotheses -> greatest ancestor                     (linearizer's responsibility, base case)
                           -> this polynomial with no cancellations (recursive case)
                           =  this polynomial                       (by fusion, outside this method)
                           -> false                                 (by some variation of `0 < c -> false`
                                                                     for e.g. `c <= 0`)
    */
    expr get_proof_messy() const {
        if (m_lazy_proof) {
            return (*m_lazy_proof)();
        } else {
            lean_assert(m_parents);
            poly const & p = m_parents->get_p();
            poly const & q = m_parents->get_q();
            expr p_proof = p.get_proof_messy();
            expr q_proof = q.get_proof_messy();
            expr p_scale_pos = prove_positive(m_parents->get_p_scale(), m_A);
            expr q_scale_pos = prove_positive(m_parents->get_q_scale(), m_A);
            expr pf_messy = get_app_builder().mk_app(get_resolve_name(), {p_proof, q_proof, p_scale_pos, q_scale_pos});
            return pf_messy;
        }
    }

    /* Only valid if [m_monomials] is non-empty */
    bool is_positive() const { return get_major_coefficient().is_pos(); }
    std::vector<atom> const & get_major_idx() const { return head(m_monomials).get_atoms(); }
    mpq const & get_major_coefficient() const { return head(m_monomials).get_coefficient(); }
};

std::ostream & operator<<(std::ostream & out, poly const & p) {
    out << "0 " << (p.is_strict() ? "<" : "<=") << " ";
    for (auto m : p.get_monomials()) out << m << " + ";
    out << p.get_offset();
    return out;
}

poly_parents::poly_parents(poly const & p, poly const & q, mpq const & p_scale, mpq const & q_scale):
    m_p(new poly(p)), m_q(new poly(q)), m_p_scale(p_scale), m_q_scale(q_scale) {}

/* Linearizer */
class linearizer {
    // TODO(dhs): I disabled the unknown tracking. If it is a performance issue, I will add it again.
    bool type_ok(expr const & A) {
        blast_tmp_type_context m_tmp_tctx;
        bool ok = static_cast<bool>(m_tmp_tctx->mk_class_instance(get_app_builder().mk_linear_ordered_comm_ring(A)));
        if (!ok) lean_trace(*g_heuristic_trace_name, tout() << "bad type: " << ppb(A) << "\n";);
        return ok;
    }
    poly linearize(expr const & A, expr const & rhs, bool strict, lazy_proof const & lproof) {
        polynomial p = arith::normalize_poly(rhs);
        return poly(A, to_list(p.get_monomials().begin(), p.get_monomials().end()), p.get_offset(), strict, lproof);
    }
public:
    list<poly> linearize(hypothesis_idx hidx) {
        hypothesis const & h = curr_state().get_hypothesis_decl(hidx);
        /* TODO(dhs): as a pre-process step, put 0 on the LHS of the inequality. */
        expr A, lhs, rhs;
        if (is_lt(h.get_type(), A, lhs, rhs) && type_ok(A)) {
            expr new_rhs = get_app_builder().mk_add(A, rhs, get_app_builder().mk_neg(A, lhs));
            return list<poly>(linearize(A, new_rhs, true, [=]() {
                        return get_app_builder().mk_app(get_ordered_arith_zero_lt_of_lt_name(), h.get_self());
                    }));
        } else if (is_le(h.get_type(), A, lhs, rhs) && type_ok(A)) {
            expr new_rhs = get_app_builder().mk_add(A, rhs, get_app_builder().mk_neg(A, lhs));
            return list<poly>(linearize(A, new_rhs, false, [=]() {
                        return get_app_builder().mk_app(get_ordered_arith_zero_le_of_le_name(), h.get_self());
                    }));
        } else if (is_eq(h.get_type(), A, lhs, rhs) && type_ok(A)) {
            expr new_rhs1 = get_app_builder().mk_add(A, rhs, get_app_builder().mk_neg(A, lhs));
            expr new_rhs2 = get_app_builder().mk_add(A, lhs, get_app_builder().mk_neg(A, rhs));
            poly p1 = linearize(A, new_rhs1, false, [=]() {
                    return get_app_builder().mk_app(get_ordered_arith_zero_le_of_eq1_name(), h.get_self());
                });
            poly p2 = linearize(A, new_rhs2, false, [=]() {
                    return get_app_builder().mk_app(get_ordered_arith_zero_le_of_eq2_name(), h.get_self());
                });
            return list<poly>({p1, p2});
        } else {
            return list<poly>();
        }
    }
};

/* Poly-pot */
class poly_pot {
    list<poly> m_positives;
    list<poly> m_negatives;
public:
    void insert(poly const & p) {
        if (p.is_positive()) {
            m_positives = cons(p, m_positives);
        } else {
            m_negatives = cons(p, m_negatives);
        }
    }
    list<poly> get_positives() { return m_positives; }
    list<poly> get_negatives() { return m_negatives; }
};

struct heuristic_branch_extension : public branch_extension {
private:
    // TODO(dhs): will this cause problems during rebalancing?
    // Should I wrap this class and make a cheap copy?
    typedef rb_map<std::vector<atom>, poly_pot, atoms_quick_cmp> poly_pot_map;
    linearizer        m_linearizer;
    poly_pot_map      m_poly_pot_map;
    list<poly>        m_todo;
public:
    heuristic_branch_extension() {}
    heuristic_branch_extension(heuristic_branch_extension const & ext):
        m_linearizer(ext.m_linearizer), m_poly_pot_map(ext.m_poly_pot_map), m_todo(ext.m_todo) {}
    virtual branch_extension * clone() override { return new heuristic_branch_extension(*this); }

    void put_todo(buffer<poly> const & todo) { m_todo = to_list(todo); }
    void get_todo(buffer<poly> & todo) {
        to_buffer(m_todo, todo);
        m_todo = list<poly>();
    }

    list<poly> linearize(hypothesis_idx hidx) { return m_linearizer.linearize(hidx); }

    poly_pot insert_poly_into_pot(poly const & p) {
        poly_pot const * pot_p = m_poly_pot_map.find(p.get_major_idx());
        poly_pot pot = (pot_p ? *pot_p : poly_pot());
        pot.insert(p);
        m_poly_pot_map.insert(p.get_major_idx(), pot);
        return pot;
    }
};

static heuristic_branch_extension & get_heuristic_extension() {
    return static_cast<heuristic_branch_extension&>(curr_state().get_extension(g_ext_id));
}

/* HEURISTIC function */
class heuristic_fn {
    heuristic_branch_extension &        m_ext;
    buffer<poly>                  m_todo;
    unsigned                      m_num_steps{0};

    optional<poly>                m_contradiction;

    /* Options */
    unsigned                      m_max_steps{get_heuristic_max_steps_per_action()};

    void register_todo(poly const & p) {
        switch (p.kind()) {
        case poly_kind::Normal:
            m_todo.push_back(p);
            lean_trace(*g_heuristic_trace_name, ios().get_diagnostic_channel() << "todo: " << p << "\n";);
            break;
        case poly_kind::Contradiction:
            lean_trace(*g_heuristic_trace_name, ios().get_diagnostic_channel() << "contradiction: " << p << "\n";);
            m_contradiction = p;
            break;
        case poly_kind::Trivial:
            lean_trace(*g_heuristic_trace_name, ios().get_diagnostic_channel() << "trivial: " << p << "\n";);
            break;
        }
    }

    void scale_monomials(list<monomial> const & monomials, mpq const & scale, buffer<monomial> & new_monomials) {
        lean_assert(!is_nil(monomials));
        list<monomial> ms = monomials;
        while (!is_nil(ms)) {
            monomial m = head(ms);
            mpq new_coefficient{0};
            addmul(new_coefficient, scale, m.get_coefficient());
            new_monomials.emplace_back(new_coefficient, m.get_atoms());
            ms = tail(ms);
        }
    }

    pair<mpq, mpq> compute_scaling_coefficients(mpq const & _p_coefficient, mpq const & _q_coefficient) {
        mpq p_scale, q_scale;

        mpq p_coefficient = _p_coefficient;
        mpq q_coefficient = _q_coefficient;
        if (p_coefficient.is_integer() && q_coefficient.is_integer()) {
            p_coefficient.abs();
            q_coefficient.abs();
            p_scale = lcm(p_coefficient.get_numerator(), q_coefficient.get_numerator());
            q_scale = p_scale;
            p_scale /= p_coefficient;
            q_scale /= q_coefficient;
        } else {
            p_scale = p_coefficient;
            p_scale.inv();
            q_scale = q_coefficient;
            q_scale.inv();
            if (p_scale < 0) {
                p_scale.neg(); lean_assert(q_scale > 0);
            } else {
                q_scale.neg(); lean_assert(p_scale > 0);
            }
        }
        return mk_pair(p_scale, q_scale);
    }

    void resolve_polys(poly const & p, poly const & q) {
        mpq p_scale, q_scale;
        std::tie(p_scale, q_scale) = compute_scaling_coefficients(p.get_major_coefficient(), q.get_major_coefficient());

        lean_trace(*g_heuristic_trace_name, ios().get_diagnostic_channel() << "resolve(" << p_scale << ", " << q_scale << "): "
                   << p << " WITH " << q << "\n";);

        list<monomial> p_monomials = p.get_monomials();
        list<monomial> q_monomials = q.get_monomials();

        lean_assert(!is_nil(p_monomials));
        lean_assert(!is_nil(q_monomials));

        buffer<monomial> new_monomials;

        /* We can skip the first element, since we know they will cancel */
        monomial p_major = head(p_monomials);
        monomial q_major = head(p_monomials);

        lean_assert(p_major.get_atoms() == q_major.get_atoms());

        p_monomials = tail(p_monomials);
        q_monomials = tail(q_monomials);

        /* Now, we proceed, advancing one iterator at a time */
        while (true) {
            if (is_nil(p_monomials) && is_nil(q_monomials)) {
                break;
            } else if (is_nil(p_monomials)) {
                scale_monomials(q_monomials, q_scale, new_monomials);
                break;
            } else if (is_nil(q_monomials)) {
                scale_monomials(p_monomials, p_scale, new_monomials);
                break;
            } else {
                monomial const & p_m = head(p_monomials);
                monomial const & q_m = head(q_monomials);
                mpq new_coefficient{0};
                if (monomial_fuse_lt()(p_m, q_m)) {
                    addmul(new_coefficient, p_scale, p_m.get_coefficient());
                    if (!new_coefficient.is_zero()) new_monomials.emplace_back(new_coefficient, p_m.get_atoms());
                    p_monomials = tail(p_monomials);
                } else if (monomial_fuse_lt()(q_m, p_m)) {
                    addmul(new_coefficient, q_scale, q_m.get_coefficient());
                    if (!new_coefficient.is_zero()) new_monomials.emplace_back(new_coefficient, q_m.get_atoms());
                    q_monomials = tail(q_monomials);
                } else {
                    addmul(new_coefficient, p_scale, p_m.get_coefficient());
                    addmul(new_coefficient, q_scale, q_m.get_coefficient());
                    if (!new_coefficient.is_zero()) new_monomials.emplace_back(new_coefficient, p_m.get_atoms());
                    p_monomials = tail(p_monomials);
                    q_monomials = tail(q_monomials);
                }
            }
        }
        mpq new_offset{0};
        addmul(new_offset, p_scale, p.get_offset());
        addmul(new_offset, q_scale, q.get_offset());

        register_todo(poly(p.get_A(), to_list(new_monomials), new_offset, poly_parents(p, q, p_scale, q_scale)));
    }

    void process_poly(poly const & p) {
        lean_assert(p.kind() == poly_kind::Normal);
        lean_assert(!is_nil(p.get_monomials()));
        poly_pot pot = m_ext.insert_poly_into_pot(p);
        list<poly> to_resolve_with = (p.is_positive() ? pot.get_negatives() : pot.get_positives());
        for (poly const & q : to_resolve_with) {
            resolve_polys(p, q);
            if (m_contradiction) break;
        }
    }

public:
    heuristic_fn(): m_ext(get_heuristic_extension()) {}

    action_result operator()(hypothesis_idx hidx) {
        /* There may me some TODO items remaining from the previous invocation. */
        m_ext.get_todo(m_todo);

        /* We convert the new hypothesis into 0, 1, or 2 polynormial inequalities. */
        list<poly> new_todo = m_ext.linearize(hidx);
        for (poly const & p : new_todo) {
            register_todo(p);
            if (m_contradiction) break;
        }

        while (!m_todo.empty() && !m_contradiction) {
            m_num_steps++;
            if (m_num_steps > m_max_steps) {
                m_ext.put_todo(m_todo);
                break;
            }
            poly p = m_todo.back();
            m_todo.pop_back();
            process_poly(p);
        }

        if (!m_contradiction) {
            // TODO(dhs): If I infer new equalities, add them as hypotheses and return a new branch.
            // (not even checking for equalities yet)
            return action_result::failed();
        } else {
            poly const & p = m_contradiction.value();
            expr const & A = p.get_A();

            expr pf_messy = p.get_proof_messy();
            expr type_messy = infer_type(pf_messy);

            expr type_clean = p.get_clean_thm();
            expr pf_messy_eq_clean; list<expr> placeholders;
            std::tie(pf_messy_eq_clean, placeholders) = arith::normalize_prove_eq(app_arg(type_messy), app_arg(type_clean), A);
            expr id_motive = get_app_builder().mk_app(get_lt_name(), 3, get_app_builder().mk_zero(A));
            expr pf_clean = get_app_builder().mk_eq_rec(id_motive, pf_messy, pf_messy_eq_clean);

            expr pf_false_of_clean;

            if (p.is_strict()) {
                if (p.get_offset().is_zero()) pf_false_of_clean = prove_zero_not_lt_zero(A);
                else pf_false_of_clean = prove_zero_not_lt_neg(A, p.get_offset());
            } else {
                pf_false_of_clean = prove_zero_not_le_neg(A, p.get_offset());
            }

            state & s = curr_state();
            expr pf_of_target = get_app_builder().mk_false_rec(s.get_target(), mk_app(pf_false_of_clean, pf_clean));
            if (is_nil(placeholders)) {
                return action_result::solved(pf_of_target);
            } else {
                s.push_proof_step(new arith_heuristic_proof_step_cell(placeholders));
                return action_result::solved(pf_of_target);
            }
        }
    }
};

/* Setup and teardown */
void initialize_heuristic() {
    g_heuristic_trace_name           = new name{"blast", "arith", "heuristic"};
    g_heuristic_max_steps_per_action = new name{"blast", "heuristic", "max_steps_per_action"};

    register_unsigned_option(*g_heuristic_max_steps_per_action, LEAN_DEFAULT_HEURISTIC_MAX_STEPS_PER_ACTION,
                             "(blast::heuristic) max steps of heuristic per action");

    g_ext_id = register_branch_extension(new heuristic_branch_extension());
    register_trace_class(*g_heuristic_trace_name);
}

void finalize_heuristic() {
    delete g_heuristic_max_steps_per_action;
    delete g_heuristic_trace_name;
}

/* Entry points */
action_result assert_arith_heuristic_action(hypothesis_idx hidx) {
    if (!get_config().m_arith_heuristic) return action_result::failed();
    lean_trace(*g_heuristic_trace_name, ios().get_diagnostic_channel() << "assert_arith_heuristic\n";);
    return heuristic_fn()(hidx);
}

}}
