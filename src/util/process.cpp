/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include <unistd.h>
#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
//
#else
#include <sys/wait.h>
#endif
#include "util/process.h"
#include "util/buffer.h"
#include "util/pipe.h"

namespace lean {
// TODO(jroesch): make this cross platform
process::process(std::string n): m_proc_name(n), m_args() {
    m_args.push_back(m_proc_name);
}

process & process::arg(std::string a) {
    m_args.push_back(a);
    return *this;
}

process & process::stdin(stdio cfg) {
    m_stdin = optional<stdio>(cfg);
    return *this;
}

process & process::stdout(stdio cfg) {
    m_stdout = optional<stdio>(cfg);
    return *this;
}

process & process::stderr(stdio cfg) {
    m_stderr = optional<stdio>(cfg);
    return *this;
}

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
void process::run() {
    throw exception("process::run not supported on Windows");
}
#else

optional<pipe> setup_stdio(optional<stdio> cfg) {
    /* Setup stdio based on process configuration. */
    if (cfg) {
        switch (*cfg) {
        /* We should need to do nothing in this case */
        case stdio::INHERIT:
            return optional<pipe>();
        case stdio::PIPED: {
            return optional<pipe>(lean::pipe());
        }
        case stdio::NUL: {
            /* We should map /dev/null. */
            return optional<pipe>();
        }
        default:
           lean_unreachable();
        }
    } else {
        return optional<pipe>();
    }
}

child process::spawn() {
    /* Setup stdio based on process configuration. */
    auto stdin_pipe = setup_stdio(m_stdin);
    auto stdout_pipe = setup_stdio(m_stdout);
    auto stderr_pipe = setup_stdio(m_stderr);

    int pid = fork();

    if (pid == 0) {
        if (stdin_pipe) {
            dup2(stdin_pipe->m_read_fd, STDIN_FILENO);
            close(stdin_pipe->m_write_fd);
        }

        if (stdout_pipe) {
            dup2(stdout_pipe->m_write_fd, STDOUT_FILENO);
            close(stdout_pipe->m_read_fd);
        }

        if (stderr_pipe) {
            dup2(stderr_pipe->m_write_fd, STDERR_FILENO);
            close(stderr_pipe->m_read_fd);
        }

        buffer<char*> pargs;

        for (auto arg : this->m_args) {
            auto str = new char[arg.size() + 1];
            arg.copy(str, arg.size());
            str[arg.size()] = '\0';
            pargs.push_back(str);
        }

        pargs.data()[pargs.size()] = NULL;

        auto err = execvp(pargs.data()[0], pargs.data());
        if (err < 0) {
            throw std::runtime_error("executing process failed: ...");
        }
    } else if (pid == -1) {
        throw std::runtime_error("forking process failed: ...");
    }

    /* We want to setup the parent's view of the file descriptors. */
    int parent_stdin = STDIN_FILENO;
    int parent_stdout = STDOUT_FILENO;
    int parent_stderr = STDERR_FILENO;

    if (stdin_pipe) {
        close(stdin_pipe->m_read_fd);
        parent_stdin = stdin_pipe->m_write_fd;
    }

    if (stdout_pipe) {
        close(stdout_pipe->m_write_fd);
        parent_stdout = stdout_pipe->m_read_fd;
    }

    if (stderr_pipe) {
        close(stderr_pipe->m_write_fd);
        parent_stderr = stderr_pipe->m_read_fd;
    }

    return child(pid, parent_stdin, parent_stdout, parent_stderr);
}

void process::run() {
    child ch = spawn();
    int status;
    waitpid(ch.m_pid, &status, 0);
}

#endif

}
