/*
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Robert Y. Lewis
*/
#include "kernel/for_each_fn.h"
#include "library/util.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/list_axioms_tactic.h"
#include "library/sorry.h"

namespace lean {

void list_axioms_deps::visit(name const & n) {
    if (m_visited.contains(n))
        return;
    m_visited.insert(n);
    declaration const & d = m_env.get(n);
    if (!d.is_definition() && !m_env.is_builtin(n)) {
        m_use_axioms = true;
        m_axioms.insert(d.get_name());
    }
    visit(d.get_type());
    if (d.is_definition())
        visit(d.get_value());
}

void list_axioms_deps::visit(expr const & e) {
    for_each(e, [&](expr const & e, unsigned) {
        if (is_sorry(e) && !m_used_sorry) {
            m_used_sorry = true;
        }
        if (is_constant(e))
            visit(const_name(e));
        return true;
    });
}

buffer<name> list_axioms_deps::axiom_list() {
    buffer<name> b = buffer<name>();
    m_axioms.to_buffer(b);
    return b;
}

vm_obj tactic_list_axioms(vm_obj const & n, vm_obj const & s0) {
    tactic_state const & s = tactic::to_state(s0);
    environment const & env = s.env();
    name nm = to_name(n);
    try {
        buffer<name> const & axiom_names = list_axioms_deps(env)(nm);
        return tactic::mk_success(to_obj(axiom_names), s);
    } catch (exception e) {
        return tactic::mk_exception(e, s);
    }
}
    
void initialize_list_axioms_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "list_axioms"}), tactic_list_axioms);
}

void finalize_list_axioms_tactic() {
}

}
