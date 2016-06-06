#include <iostream>
#include "util/numerics/mpz.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm.h"
#include "init/init.h"

namespace lean {
lean::vm_obj put_nat(lean::vm_obj const &);
}
lean::vm_obj ___lean__main() {
return lean::put_nat(lean::mk_vm_mpz(lean::mpz(1)));
}
int main() {
___lean__main();
return 0;
}
