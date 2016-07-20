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
        std::string m_proc_name;
        buffer<std::string> m_args;
    public:
        // TODO: make this cross platform
        process(std::string exe_name);
        process & arg(std::string arg_str);
        void run();
    };

    class cpp_compiler {
      buffer<std::string> m_library_paths;
      buffer<std::string> m_include_paths;
      buffer<std::string> m_files;
      buffer<std::string> m_link;

      bool m_debug;

    public:
        cpp_compiler & link(std::string lib);
        cpp_compiler & library_path(std::string lib_path);
        cpp_compiler & include_path(std::string include_path);
        cpp_compiler & debug(bool on);
        cpp_compiler & file(std::string file_path);
        cpp_compiler();
        void run();
    };
}
