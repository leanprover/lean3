/*
Author: James King <james@agenultra.com>
*/

#include <dlfcn.h>

void get_shared_funcptr(const char * pathname) {
      void* handle = dlopen("libpq.so", RTLD_LAZY);
      if (!handle) {
        cerr << "Cannot load library: " << dlerror() << '\n';
      }
}
