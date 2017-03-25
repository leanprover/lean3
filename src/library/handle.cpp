/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author:  Leonardo de Moura & Jared Roesch
*/
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include <unistd.h>
#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#include <windows.h>
#include <tchar.h>
#include <stdio.h>
#include <strsafe.h>

#define BUFSIZE 4096
#else
#include <sys/wait.h>
#endif
#include "library/process.h"
#include "library/handle.h"
#include "util/buffer.h"
#include "library/pipe.h"
#include "unistd.h"
#include "stdio.h"

namespace lean {

void handle::write(buffer<char> & buf) {
    auto sz = buf.size();
    if (fwrite(buf.data(), 1, sz, m_file) != sz) {
        std::cout << "write_error: " << errno << std::endl;
        clearerr(m_file);
        throw handle_exception("write failed");
    }
}

void handle::flush() {
    if (fflush(m_file) != 0) {
        clearerr(m_file);
        throw handle_exception("flush failed");
    }
}

handle::~handle() {
    if (m_file && m_file != stdin &&
        m_file != stderr && m_file != stdout)
    {
        fclose(m_file);
    }
}

bool handle::is_stdin() {
    return m_file == stdin;
}

bool handle::is_stdout() {
    return m_file == stdout;
}

bool handle::is_stderr() {
    return m_file == stderr;
}

void handle::close() {
    if (fclose(m_file) == 0) {
        m_file = nullptr;
    } else {
        clearerr(m_file);
        throw handle_exception("close failed");
    }
}

bool handle::is_closed() {
   return !m_file;
}

}
