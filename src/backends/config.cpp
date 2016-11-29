/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <iostream>
#include <sstream>
#include <memory>
#include <tuple>
#include <utility>
#include "backend.h"
#include "free_vars.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/app_builder.h"
#include "library/extern.h"
#include "library/normalize.h"
#include "library/let.h"
#include "library/trace.h"
#include "used_names.h"
#include "util/fresh_name.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {
    config::config(optional<std::string> main_fn, optional<std::string> output_path) {
        if (main_fn) {
            this->m_main_fn = main_fn.value();
        } else {
            this->m_main_fn = "main";
        }

        if (output_path) {
            this->m_output_path = output_path.value();
        } else {
            this->m_output_path = "main";
        }
    }
}
