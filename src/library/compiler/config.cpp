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
#include "config.h"

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
