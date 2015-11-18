/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/choice_point.h"
#include "library/blast/simple_actions.h"
#include "library/blast/proof_expr.h"
#include "library/blast/intros_action.h"
#include "library/blast/no_confusion_action.h"
#include "library/blast/subst_action.h"
#include "library/blast/backward/backward_rule_set.h"
#include "library/blast/backward/backward_action.h"
#include "library/blast/strategy.h"

namespace lean {
namespace blast {
/** \brief Basic backwards chaining, inspired by Coq's [auto]. */
class backward_strategy : public strategy {
    virtual optional<expr> preprocess() override { return none_expr(); }

    action_result activate_hypothesis() {
        optional<hypothesis_idx> hidx = curr_state().activate_hypothesis();
        if (!hidx) return action_result::failed();
        trace_action("activate");

        Try(assumption_contradiction_actions(*hidx));
        Try(subst_action(*hidx));
        Try(no_confusion_action(*hidx));
        Try(discard_action(*hidx));
        return action_result::new_branch();
    }

    virtual action_result next_action() override {
        Try(intros_action());
        Try(activate_hypothesis());
        Try(trivial_action());
        Try(assumption_action());
        list<gexpr> backward_rules = curr_state().get_backward_rule_set().find(head_index(curr_state().get_target()));
        Try(backward_action(backward_rules, true));
        return action_result::failed();
    }
};

optional<expr> apply_backward_strategy() {
    return backward_strategy()();
}
}}
