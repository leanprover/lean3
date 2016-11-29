/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include "util/exception.h"
#include "util/sexpr/options.h"
#include "kernel/formatter.h"
#include "kernel/expr.h"

namespace lean {
/** \brief Base class for exceptions with support for pretty printing. */
class backend_exception : public exception {
public:
    backend_exception() {}
    backend_exception(char const * msg):exception(msg) {}
    backend_exception(sstream const & strm):exception(strm) {}
    virtual ~backend_exception() noexcept {}
    /** \brief Return a reference (if available) to the main expression associated with this exception.
        This information is used to provide better error messages. */
    virtual optional<expr> get_main_expr() const { return none_expr(); }
    virtual format pp(formatter const &) const { return format(what()); }
    virtual throwable * clone() const { return new backend_exception(m_msg.c_str()); }
    virtual void rethrow() const { throw *this; }
};
}
