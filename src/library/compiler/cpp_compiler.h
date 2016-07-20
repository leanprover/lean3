/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "unistd.h"
#include "kernel/environment.h"
#include "kernel/expr.h"

namespace lean  {

    class process {
    public:
        process(std::string exe_name) {
            int pid = fork();
            if (pid == 0) {
                std::cout << "in the child" << std
                exec(exe_name.c_str(), (char *) null);
            } else {
                std::cout << "in the parent" << std::endl;
            }
        }
    };

    class cpp_compiler {
    public:
        cpp_compiler();
    };
}
