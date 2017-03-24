/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author:  Leonardo de Moura & Jared Roesch
*/
#pragma once

#include <iostream>
#include <string>
#include "util/buffer.h"
#include "pipe.h"

struct handle {
    FILE * m_handle;
    handle(FILE * h):m_handle(h) {}
    ~handle() { if (m_handle && m_handle != stdin && m_handle != stderr && m_handle != stdout) fclose(m_handle); }
};

typedef std::shared_ptr<handle> handle_ref;
