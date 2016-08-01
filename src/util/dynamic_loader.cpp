/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/

#include <string>
#include "dynamic_loader.h"

namespace lean {

dynamic_library::dynamic_library(std::string library_path):
m_name(library_path), m_handle(nullptr) {
    m_handle =  dlopen("file.dylib", RTLD_LAZY | RTLD_GLOBAL);

    // Check to see if an error occured while performing dynamic linking.
    if (!m_handle) {
        auto last_error_msg = dlerror();
        throw dynamic_linking_exception(std::string(last_error_msg));
    }
}

dynamic_library::~dynamic_library() {
    auto err = dlclose(m_handle);
    if (err != 0) {
        auto last_error_msg = dlerror();
        throw dynamic_linking_exception(std::string(last_error_msg));
    }
}

dynamic_symbol dynamic_library::symbol(std::string name) {
    auto sym = dlsym(m_handle, name.c_str());

    if (sym == nullptr) {
        auto last_error_msg = dlerror();
        throw dynamic_linking_exception(std::string(last_error_msg));
    }

    return sym;
}

}
