/*
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Robert Y. Lewis
*/

#pragma once
#include "util/name_set.h"

namespace lean {

struct list_axioms_deps {
    environment     m_env;
    name_set        m_visited;
    name_set        m_axioms;
    bool            m_use_axioms;
    bool            m_used_sorry;
    list_axioms_deps(environment const & env):
        m_env(env), m_use_axioms(false), m_used_sorry(false) {}

    void visit(name const & n);
    void visit(expr const & e);
    buffer<name> axiom_list();
    buffer<name> operator()(name const & n) {
        visit(n);
        return axiom_list();
   }
};

void initialize_list_axioms_tactic();
void finalize_list_axioms_tactic();

}
