
#include <stdio.h>
#include <dlfcn.h>


int main () {
      int (*my_main) ();
      void* handle = dlopen("some_file.so", RTLD_LAZY);
      if (!handle) {
        printf("Cannot load library: %s", dlerror());
        return -1;
      }
      my_main = dlsym(handle, "main");
      if (!my_main) {
        printf("Cannot load 'main': %s", dlerror());
        return -1;
      }
      my_main();
}
