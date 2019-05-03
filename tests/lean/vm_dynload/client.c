
#include <ffi.h>
#include <stdio.h>
#include <dlfcn.h>

typedef int (*main_fn) (int, int);

void call(main_fn fn, int x, int y) {
    ffi_cif cif;
    ffi_type *args[2] = {&ffi_type_sint32, &ffi_type_sint32};
    void *values[2] = {(void *) &x, (void *) &y};
    ffi_arg rc;
    if (ffi_prep_cif(&cif, FFI_DEFAULT_ABI, 2,
		       &ffi_type_sint32, args) == FFI_OK)
    {
      /* s = "Hello World!"; */
        ffi_call(&cif, (void (*)(void)) fn, &rc, values);
        printf("result: %d", (int) rc);
    }

    /* char *s; */
    /* ffi_arg rc; */

    /* Initialize the argument info vectors */
    /* args[0] = &ffi_int; */
    /* values[0] = &s; */

}

int main () {
    main_fn my_main;
    void* handle = dlopen("some_file.so", RTLD_LAZY);
    if (!handle) {
        printf("Cannot load library: %s", dlerror());
        return -1;
    }
    my_main = dlsym(handle, "my_fun");
    if (!my_main) {
        printf("Cannot load 'main': %s", dlerror());
        return -1;
    }
    call(my_main,2,3);
}
