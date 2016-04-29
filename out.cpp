#include "lean_runtime.h"

#include "string.h"

static lean::obj string_empty = lean::mk_obj(0);

lean::obj prod_mk_direct(lean::obj f0, lean::obj f1) {
return lean::mk_obj(0, { f0, f1 });
}

static lean::obj bool_tt = lean::mk_obj(1);

static lean::obj bool_ff = lean::mk_obj(0);

static lean::obj RealWorld_mk = lean::mk_obj(0);

lean::obj char_mk_direct(lean::obj f0, lean::obj f1, lean::obj f2, lean::obj f3, lean::obj f4, lean::obj f5, lean::obj f6, lean::obj f7) {
return lean::mk_obj(0, { f0, f1, f2, f3, f4, f5, f6, f7 });
}

lean::obj string_str_direct(lean::obj f0, lean::obj f1) {
return lean::mk_obj(1, { f0, f1 });
}

lean::obj ___lean__main_direct();
static lean::obj ___lean__main = mk_closure(___lean__main_direct, 0, 0, nullptr);
lean::obj prod_rec_on_direct(lean::obj __lean_nv_18_410, lean::obj __lean_nv_18_411);
static lean::obj prod_rec_on = mk_closure(prod_rec_on_direct, 0, 0, nullptr);
lean::obj print_string_direct(lean::obj __lean_nv_18_414);
static lean::obj print_string = mk_closure(print_string_direct, 0, 0, nullptr);
lean::obj prod_rec_direct(lean::obj __lean_nv_arg_18_412, lean::obj __lean_nv_arg_18_413);
static lean::obj prod_rec = mk_closure(prod_rec_direct, 0, 0, nullptr);
lean::obj ___lean__main_direct() {
lean::obj __lean_nv_18_386 = char_mk_direct(bool_ff, bool_tt, bool_ff, bool_ff, bool_tt, bool_ff, bool_ff, bool_ff);
lean::obj __lean_nv_18_388 = char_mk_direct(bool_ff, bool_tt, bool_tt, bool_ff, bool_ff, bool_tt, bool_ff, bool_tt);
lean::obj __lean_nv_18_390 = char_mk_direct(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_ff, bool_ff);
lean::obj __lean_nv_18_392 = char_mk_direct(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_ff, bool_ff);
lean::obj __lean_nv_18_394 = char_mk_direct(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_tt, bool_tt);
lean::obj __lean_nv_18_396 = char_mk_direct(bool_ff, bool_ff, bool_tt, bool_ff, bool_ff, bool_ff, bool_ff, bool_ff);
lean::obj __lean_nv_18_398 = char_mk_direct(bool_ff, bool_tt, bool_ff, bool_ff, bool_tt, bool_tt, bool_ff, bool_ff);
lean::obj __lean_nv_18_400 = char_mk_direct(bool_ff, bool_tt, bool_tt, bool_ff, bool_ff, bool_tt, bool_ff, bool_tt);
lean::obj __lean_nv_18_402 = char_mk_direct(bool_ff, bool_tt, bool_tt, bool_ff, bool_ff, bool_ff, bool_ff, bool_tt);
lean::obj __lean_nv_18_404 = char_mk_direct(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_tt, bool_ff);
lean::obj __lean_nv_18_406 = char_mk_direct(bool_ff, bool_ff, bool_tt, bool_ff, bool_ff, bool_ff, bool_ff, bool_tt);
lean::obj __lean_nv_18_405 = string_str_direct(__lean_nv_18_406, string_empty);
lean::obj __lean_nv_18_403 = string_str_direct(__lean_nv_18_404, __lean_nv_18_405);
lean::obj __lean_nv_18_401 = string_str_direct(__lean_nv_18_402, __lean_nv_18_403);
lean::obj __lean_nv_18_399 = string_str_direct(__lean_nv_18_400, __lean_nv_18_401);
lean::obj __lean_nv_18_397 = string_str_direct(__lean_nv_18_398, __lean_nv_18_399);
lean::obj __lean_nv_18_395 = string_str_direct(__lean_nv_18_396, __lean_nv_18_397);
lean::obj __lean_nv_18_393 = string_str_direct(__lean_nv_18_394, __lean_nv_18_395);
lean::obj __lean_nv_18_391 = string_str_direct(__lean_nv_18_392, __lean_nv_18_393);
lean::obj __lean_nv_18_389 = string_str_direct(__lean_nv_18_390, __lean_nv_18_391);
lean::obj __lean_nv_18_387 = string_str_direct(__lean_nv_18_388, __lean_nv_18_389);
lean::obj __lean_nv_18_385 = string_str_direct(__lean_nv_18_386, __lean_nv_18_387);
return print_string_direct(__lean_nv_18_385);
}

lean::obj prod_rec_on_direct(lean::obj __lean_nv_18_410, lean::obj __lean_nv_18_411) {
return prod_rec_direct(__lean_nv_18_411, __lean_nv_18_410);
}

lean::obj print_string_direct(lean::obj __lean_nv_18_414) {
lean::obj __lean_nv_18_416 = string_to_raw_string_direct(RealWorld_mk, __lean_nv_18_414);
return prod_rec_on_direct(__lean_nv_18_416, raw_print);
}

lean::obj prod_rec_direct(lean::obj __lean_nv_arg_18_412, lean::obj __lean_nv_arg_18_413) {
switch (__lean_nv_arg_18_413.cidx()) {
default:
lean::runtime_error("recursor-compilation-failure");
break;
}
}

int main() {
lean::run_lean_main(___lean__main_direct);
return 0;
}
