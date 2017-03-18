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
int setup_stdio(int file_descriptor, stdio cfg) {
    switch (cfg) {
        /* We should need to do nothing in this case */
        case stdio::INHERIT:
            return file_descriptor;
        case stdio::PIPED:
            int pipe_fds[2];
            if (pipe(pipe_fds) == -1) {
                throw exception("unable to create pipe between child process");
            }
            /* We should setup a new pipe */
            break;
        case stdio::NUL:
            /* We should map /dev/null. */
            break;
    }
}

child process::spawn() {
    int child_stdin = STDIN_FILENO;
    int stdin_pipe[2];
    int stdout_pipe[2];

    /* Setup stdio based on process configuration. */
    if (m_stdin) {
        switch (*m_stdin) {
        /* We should need to do nothing in this case */
        case stdio::INHERIT:
            break;
        case stdio::PIPED: {
            std::cout << "redirecting STDIN" << std::endl;
            if (pipe(stdin_pipe) == -1) {
                throw exception("unable to create pipe between child process");
            }
            std::cout << stdin_pipe[0] << " " << stdin_pipe[1] << std::endl;
            /* We should setup a new pipe */
            break;
        }
        case stdio::NUL:
            /* We should map /dev/null. */
            break;
        }
    }

     /* Setup stdio based on process configuration. */
    if (m_stdout) {
        switch (*m_stdout) {
        /* We should need to do nothing in this case */
        case stdio::INHERIT:
            break;
        case stdio::PIPED: {
            std::cout << "about to pipe output here" << std::endl;
            if (pipe(stdout_pipe) == -1) {
                throw exception("unable to create pipe between child process");
            }
            std::cout << stdout_pipe[0] << " " << stdout_pipe[1] << std::endl;
            /* We should setup a new pipe */
            break;
        }
        case stdio::NUL:
            /* We should map /dev/null. */
            break;
        }
    }

    int pid = fork();

    if (pid == 0) {
        // if (stdin_pipes[0] != -1) {
            dup2(stdin_pipe[0], STDIN_FILENO);
            dup2(stdout_pipe[1], STDOUT_FILENO);

            close(stdin_pipe[1]);
            close(stdout_pipe[0]);
        // }

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

    close(stdin_pipe[0]);
    close(stdout_pipe[1]);
    std::cout << stdin_pipe[1] << " " << stdout_pipe[0] << std::endl;
    return child(pid, stdin_pipe[1], stdout_pipe[0], STDERR_FILENO);
}

void process::run() {
    child ch = spawn();
    int status;
    waitpid(ch.m_pid, &status, 0);
}

#endif

}
