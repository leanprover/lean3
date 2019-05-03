/*
Author: James King <james@agenultra.com>
*/

#include <dlfcn.h>
#include <string>
#include <iostream>
#include <sys/types.h>

#include "util/sstream.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_dynload.h"

// void get_shared_funcptr(string const & pathname) {
//     void* handle = dlopen(pathname.c_str(), RTLD_LAZY);
//     if (!handle) {
//         std::cerr << "Cannot load library: " << dlerror() << '\n';
//     }
// }

namespace lean {
using namespace std;

    vm_cfunction vm_foreign_obj::get_cfun(string const & fun_name) {
        return reinterpret_cast<vm_cfunction>(dlsym(m_handle, fun_name.c_str()));
    }

    vm_foreign_obj::~vm_foreign_obj() {
        dlclose(m_handle);
    }

    shared_ptr<vm_foreign_obj> load_foreign_obj(string const & fname) {
        FOREIGN_OBJ handle = dlopen(fname.c_str(), RTLD_LAZY);
        if (!handle) {
            throw exception(sstream() << "failed to load foreign lib: " << dlerror());
        }
        return make_shared<vm_foreign_obj>(vm_foreign_obj(handle, fname));
    }

}
