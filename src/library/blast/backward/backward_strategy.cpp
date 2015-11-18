/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/blast.h"
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
    /* \brief Build the <tt>backward_rule_set</tt>. If this is too costly,
       we can maintain this set in the blast state. */
    virtual optional<expr> preprocess() override { return none_expr(); }

    action_result activate_hypothesis(bool preprocess) {
        auto hidx = curr_state().activate_hypothesis();
        if (!hidx) return action_result::failed();

        if (!preprocess) display_action("activate");

        if (auto pr = assumption_contradiction_actions(*hidx)) {
            if (!preprocess) display_action("assumption-contradiction");
            return action_result::solved(*pr);
        }

        if (subst_action(*hidx)) {
            if (!preprocess) display_action("subst");
            return action_result::new_branch();
        }

        action_result r = no_confusion_action(*hidx);
        if (!failed(r)) {
            if (!preprocess) display_action("no_confusion");
            return r;
        }

        return action_result::new_branch();
    }

    virtual action_result next_action() override {
        if (intros_action()) {
            display_action("intros");
            return action_result::new_branch();
        }

        action_result r = activate_hypothesis(false);
        if (!failed(r)) return r;

        if (auto pr = trivial_action()) {
            display_action("trivial");
            return action_result::solved(*pr);
        }

        if (auto pr = assumption_action()) {
            // Remark: this action is only relevant
            // when the target has been modified.
            display_action("assumption");
            return action_result::solved(*pr);
        }

        list<gexpr> backward_rules = curr_state().get_backward_rule_set().find(head_index(curr_state().get_target()));

        r = backward_action(backward_rules, true);
        if (!failed(r)) {
            display_action("backward");
            return r;
        }

        display_msg(">>> FAILED <<<");
        return action_result::failed();
    }
};

optional<expr> apply_backward_strategy() {
    return backward_strategy()();
}
}}
