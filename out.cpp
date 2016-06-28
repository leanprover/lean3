#include <iostream>
#include "util/numerics/mpz.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm.h"
#include "init/init.h"

namespace lean {
lean::vm_obj put_str(lean::vm_obj const &);
}
lean::vm_obj string_empty(){
lean::mk_vm_simple(0)}
lean::vm_obj char_of_nat(lean::vm_obj _$local_0){
cases_on nat.decidable_lt M.305 256
}
lean::vm_obj nat_add__rec_1(lean::vm_obj _$local_1, lean::vm_obj _$local_0){
vm::obj scrutinee = _$local_0;

if (is_simple(scrutinee)){
unsigned val = cidx(scrutinee);
if (val == 0) {
_$local_1;
}
   else {
lean::nat_succ(nat_add__rec_1(, ));
}
}
else {
mpz const & val = to_mpz(top);
if (val == 0) {
_$local_1;
}
   else {
lean::nat_succ(nat_add__rec_1(, ))}
}
}
lean::vm_obj nat_add(lean::vm_obj _$local_1, lean::vm_obj _$local_0){
nat_add__rec_1(, )}
lean::vm_obj string_str(lean::vm_obj _$local_1, lean::vm_obj _$local_0){
lean::mk_vm_constructor(1, {_$local_1, _$local_0})}
lean::vm_obj ___lean__main(){
lean::put_str(string_str(char_of_nat(lean::mk_vm_mpz(lean::mpz(65))), string_empty))}
int main() {
___lean__main();
return 0;
}
