    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <iostream>
#include <utility>
#include "c_backend.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {
    void simple_expr::display(std::ostream& os) const {
        os << "hello world";
    }

    std::ostream& operator<<(std::ostream& os, const simple_expr & se) {
        se.display(os);
        return os;
    }

    name var_name(simple_expr const & se) {
        // assert it is teh right type
        //auto ref = static_cast<simple_expr_var const &>(se);
        //return ref.m_name;
        return name("a_var");
    }
}
