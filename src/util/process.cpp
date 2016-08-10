/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include "util/process.h"
#include "util/buffer.h"
#include "unistd.h"
#include "sys/wait.h"

namespace lean {

// TODO: make this cross platform

process::process(std::string n): m_proc_name(n), m_args() {
    m_args.push_back(m_proc_name);
}

process & process::arg(std::string a) {
    m_args.push_back(a);
    return *this;
}

void process::run() {
    int pid = fork();
    if (pid == 0) {
        buffer<char*> pargs;
        for (auto arg : m_args) {
            std::cout << arg << std::endl;
            auto str = (char*)malloc(sizeof(char) * 100);
            arg.copy(str, arg.size());
            str[arg.size()] = '\0';
            // std::cout << str << std::endl;
            pargs.push_back(str);
        }

        pargs.data()[pargs.size()] = NULL;

        auto err = execvp(pargs.data()[0], pargs.data());
        if (err < 0) {
            throw std::runtime_error("executing process failed: ...");
        }
    } else if (pid == -1) {
        throw std::runtime_error("forking process failed: ...");
    } else {
        int status;
        waitpid(pid, &status, 0);
    }
}
}
