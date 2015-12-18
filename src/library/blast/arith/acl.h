/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/action_result.h"
#include "library/blast/hypothesis.h"

namespace lean {
namespace blast {

action_result assert_acl_action(hypothesis_idx hidx);
void initialize_acl();
void finalize_acl();

}}
