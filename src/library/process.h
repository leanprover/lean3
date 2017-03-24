/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include <string>
#include "library/handle.h"
#include "util/buffer.h"
#include "pipe.h"

// #if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
// #include "windows.h"
// #endif

namespace lean  {

enum stdio {
    INHERIT,
    PIPED,
    NUL,
};

struct child {
    handle_ref m_stdin;
    handle_ref m_stdout;
    handle_ref m_stderr;
    int m_pid;

    child(child const & ch) :
        m_stdin(ch.m_stdin),
        m_stdout(ch.m_stdout),
        m_stderr(ch.m_stderr),
        m_pid(ch.m_pid) {}

    child(int pid, handle_ref stdin, handle_ref stdout, handle_ref stderr) :
        m_stdin(stdin),
        m_stdout(stdout),
        m_stderr(stderr),
        m_pid(pid) {}

    void wait();
};

class process {
    std::string m_proc_name;
    buffer<std::string> m_args;
    optional<stdio> m_stdout;
    optional<stdio> m_stdin;
    optional<stdio> m_stderr;
public:
    process(process const & proc) :
        m_proc_name(proc.m_proc_name),
        m_args(proc.m_args),
        m_stdout(proc.m_stdout),
        m_stdin(proc.m_stdin),
        m_stderr(proc.m_stderr) {}
    process(std::string exe_name);
    process & arg(std::string arg_str);
    process & stdin(stdio cfg);
    process & stdout(stdio cfg);
    process & stderr(stdio cfg);
    child spawn();
    void run();
};
}
