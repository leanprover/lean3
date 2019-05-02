/*
Author: James King <james@agenultra.com>
*/

#include <dlfcn.h>
#include <string>
#include <sys/types.h>

#include "util/sstream.h"
#include "library/vm/vm_io.h"

#define FOREIGN_OBJ void *

void get_shared_funcptr(const char * pathname) {
    void* handle = dlopen("libpq.so", RTLD_LAZY);
    if (!handle) {
      cerr << "Cannot load library: " << dlerror() << '\n';
    }
}

struct vm_foreign_obj : public vm_external {
    FOREIGN_OBJ m_handle;
    char * m_filename;

    vm_foreign_obj(FOREIGN_OBJ handle, const char & filename)
      : m_handle(handle),
        m_filename(filename) {};
    virtual ~vm_foreign_obj() {}
    virtual void dealloc() override {
        this->~vm_foreign_obj();
        get_vm_allocator().deallocate(sizeof(vm_foreign_obj), this);
    }
    virtual vm_external * clone(vm_clone_fn const &) override {
      return new vm_foreign_obj(m_fd, m_filename);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {
      lean_unreachable();
    }
}

static vm_obj mk_foreign_obj(FOREIGN_OBJ handle, const char & fname) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_foreign_obj))) vm_foreign_obj(handle, fname));
}

static vm_obj load_foreign_obj(vm_obj const & fname) {
    FOREIGN_OBJ handle = dlopen(fname, RTLD_LAZY);
    if (!handle) {
        return mk_io_failure(sstream() << "failed to load foreign lib: " << dlerror());
    }
    return mk_io_result(mk_foreign_obj(handle, fname);
}
