/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include "util/optional.h"

namespace lean  {

class config {
public:
    std::string m_main_fn;
    std::string m_output_path;
    config(optional<std::string> main_fn, optional<std::string> output_path);
};

}
