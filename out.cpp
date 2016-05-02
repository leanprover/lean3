#include "lean_runtime.h"

#include "string.h"

lean::obj IO_mk_fn_ptr(lean::obj f0) {
return lean::mk_obj(0, { f0 });
}

static lean::obj string_empty = lean::mk_obj(0);

lean::obj prod_mk_fn_ptr(lean::obj f0, lean::obj f1) {
return lean::mk_obj(0, { f0, f1 });
}

static lean::obj bool_tt = lean::mk_obj(1);

static lean::obj bool_ff = lean::mk_obj(0);

lean::obj ToString_mk_fn_ptr(lean::obj f0) {
return lean::mk_obj(0, { f0 });
}

lean::obj char_mk_fn_ptr(lean::obj f0, lean::obj f1, lean::obj f2, lean::obj f3, lean::obj f4, lean::obj f5, lean::obj f6, lean::obj f7) {
return lean::mk_obj(0, { f0, f1, f2, f3, f4, f5, f6, f7 });
}

lean::obj string_str_fn_ptr(lean::obj f0, lean::obj f1) {
return lean::mk_obj(1, { f0, f1 });
}

lean::obj ToString_string_fn_ptr();
static lean::obj ToString_string = mk_closure(ToString_string_fn_ptr, 0, 0, nullptr);
lean::obj ___lean__main_fn_ptr();
static lean::obj ___lean__main = mk_closure(___lean__main_fn_ptr, 0, 0, nullptr);
lean::obj id_fn_ptr(lean::obj __$lean$_$18_74);
static lean::obj id = mk_closure(id_fn_ptr, 0, 0, nullptr);
lean::obj ToString_rec_fn_ptr(lean::obj __$lean$_$18_140, lean::obj major_premise);
static lean::obj ToString_rec = mk_closure(ToString_rec_fn_ptr, 0, 0, nullptr);
lean::obj prod_cases_on_fn_ptr(lean::obj __$lean$_$18_78, lean::obj __$lean$_$18_79);
static lean::obj prod_cases_on = mk_closure(prod_cases_on_fn_ptr, 0, 0, nullptr);
lean::obj print_line_fn_ptr(lean::obj __$lean$_$18_98, lean::obj __$lean$_$18_99);
static lean::obj print_line = mk_closure(print_line_fn_ptr, 2, 0, nullptr);
lean::obj IO_runIO_fn_ptr(lean::obj __$lean$_$18_102);
static lean::obj IO_runIO = mk_closure(IO_runIO_fn_ptr, 0, 0, nullptr);
lean::obj IO_rec_fn_ptr(lean::obj __$lean$_$18_112, lean::obj major_premise);
static lean::obj IO_rec = mk_closure(IO_rec_fn_ptr, 0, 0, nullptr);
lean::obj print_string_fn_ptr(lean::obj __$lean$_$18_116);
static lean::obj print_string = mk_closure(print_string_fn_ptr, 0, 0, nullptr);
lean::obj __$lean$_$_$closure$_18_83_fn_ptr(lean::obj __$lean$_$18_79, lean::obj __$lean$_$18_84, lean::obj __$lean$_$18_85);
static lean::obj __$lean$_$_$closure$_18_83 = mk_closure(__$lean$_$_$closure$_18_83_fn_ptr, 0, 0, nullptr);
lean::obj __$lean$_$_$closure$_18_107_fn_ptr(lean::obj __$lean$_$18_108);
static lean::obj __$lean$_$_$closure$_18_107 = mk_closure(__$lean$_$_$closure$_18_107_fn_ptr, 0, 0, nullptr);
lean::obj __$lean$_$_$closure$_18_155_fn_ptr(lean::obj __$lean$_$18_146, lean::obj __$lean$_$18_147, lean::obj __$lean$_$18_156);
static lean::obj __$lean$_$_$closure$_18_155 = mk_closure(__$lean$_$_$closure$_18_155_fn_ptr, 0, 0, nullptr);
lean::obj __$lean$_$_$closure$_18_120_fn_ptr(lean::obj __$lean$_$18_116, lean::obj __$lean$_$18_121);
static lean::obj __$lean$_$_$closure$_18_120 = mk_closure(__$lean$_$_$closure$_18_120_fn_ptr, 0, 0, nullptr);
lean::obj __$lean$_$_$closure$_18_159_fn_ptr(lean::obj __$lean$_$18_147, lean::obj __$lean$_$18_160, lean::obj __$lean$_$18_161);
static lean::obj __$lean$_$_$closure$_18_159 = mk_closure(__$lean$_$_$closure$_18_159_fn_ptr, 0, 0, nullptr);
lean::obj __$lean$_$_$closure$_18_126_fn_ptr(lean::obj __$lean$_$18_123, lean::obj __$lean$_$18_127);
static lean::obj __$lean$_$_$closure$_18_126 = mk_closure(__$lean$_$_$closure$_18_126_fn_ptr, 0, 0, nullptr);
lean::obj __$lean$_$_$closure$_18_135_fn_ptr(lean::obj __$lean$_$18_136);
static lean::obj __$lean$_$_$closure$_18_135 = mk_closure(__$lean$_$_$closure$_18_135_fn_ptr, 0, 0, nullptr);
lean::obj raw_print_io_fn_ptr(lean::obj __$lean$_$18_123);
static lean::obj raw_print_io = mk_closure(raw_print_io_fn_ptr, 0, 0, nullptr);
lean::obj ToString_to_string_fn_ptr(lean::obj __$lean$_$18_130);
static lean::obj ToString_to_string = mk_closure(ToString_to_string_fn_ptr, 1, 0, nullptr);
lean::obj prod_rec_fn_ptr(lean::obj __$lean$_$18_91, lean::obj major_premise);
static lean::obj prod_rec = mk_closure(prod_rec_fn_ptr, 0, 0, nullptr);
lean::obj bind_fn_ptr(lean::obj __$lean$_$18_146, lean::obj __$lean$_$18_147);
static lean::obj bind = mk_closure(bind_fn_ptr, 0, 0, nullptr);
lean::obj ToString_string_fn_ptr() {
lean::obj __$lean$_$18_50 = id;
return ToString_mk_fn_ptr(__$lean$_$18_50);
}

lean::obj ___lean__main_fn_ptr() {
lean::obj __$lean$_$18_52 = char_mk_fn_ptr(bool_ff, bool_tt, bool_ff, bool_ff, bool_tt, bool_ff, bool_ff, bool_ff);
lean::obj __$lean$_$18_54 = char_mk_fn_ptr(bool_ff, bool_tt, bool_tt, bool_ff, bool_ff, bool_tt, bool_ff, bool_tt);
lean::obj __$lean$_$18_56 = char_mk_fn_ptr(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_ff, bool_ff);
lean::obj __$lean$_$18_58 = char_mk_fn_ptr(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_ff, bool_ff);
lean::obj __$lean$_$18_60 = char_mk_fn_ptr(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_tt, bool_tt);
lean::obj __$lean$_$18_62 = char_mk_fn_ptr(bool_ff, bool_ff, bool_tt, bool_ff, bool_ff, bool_ff, bool_ff, bool_ff);
lean::obj __$lean$_$18_64 = char_mk_fn_ptr(bool_ff, bool_tt, bool_ff, bool_ff, bool_tt, bool_tt, bool_ff, bool_ff);
lean::obj __$lean$_$18_66 = char_mk_fn_ptr(bool_ff, bool_tt, bool_tt, bool_ff, bool_ff, bool_tt, bool_ff, bool_tt);
lean::obj __$lean$_$18_68 = char_mk_fn_ptr(bool_ff, bool_tt, bool_tt, bool_ff, bool_ff, bool_ff, bool_ff, bool_tt);
lean::obj __$lean$_$18_70 = char_mk_fn_ptr(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_tt, bool_ff);
lean::obj __$lean$_$18_72 = char_mk_fn_ptr(bool_ff, bool_ff, bool_tt, bool_ff, bool_ff, bool_ff, bool_ff, bool_tt);
lean::obj __$lean$_$18_71 = string_str_fn_ptr(__$lean$_$18_72, string_empty);
lean::obj __$lean$_$18_69 = string_str_fn_ptr(__$lean$_$18_70, __$lean$_$18_71);
lean::obj __$lean$_$18_67 = string_str_fn_ptr(__$lean$_$18_68, __$lean$_$18_69);
lean::obj __$lean$_$18_65 = string_str_fn_ptr(__$lean$_$18_66, __$lean$_$18_67);
lean::obj __$lean$_$18_63 = string_str_fn_ptr(__$lean$_$18_64, __$lean$_$18_65);
lean::obj __$lean$_$18_61 = string_str_fn_ptr(__$lean$_$18_62, __$lean$_$18_63);
lean::obj __$lean$_$18_59 = string_str_fn_ptr(__$lean$_$18_60, __$lean$_$18_61);
lean::obj __$lean$_$18_57 = string_str_fn_ptr(__$lean$_$18_58, __$lean$_$18_59);
lean::obj __$lean$_$18_55 = string_str_fn_ptr(__$lean$_$18_56, __$lean$_$18_57);
lean::obj __$lean$_$18_53 = string_str_fn_ptr(__$lean$_$18_54, __$lean$_$18_55);
lean::obj __$lean$_$18_51 = string_str_fn_ptr(__$lean$_$18_52, __$lean$_$18_53);
return run_io_main(print_line.apply(ToString_string, __$lean$_$18_51));
}

lean::obj id_fn_ptr(lean::obj __$lean$_$18_74) {
return __$lean$_$18_74;
}

lean::obj ToString_rec_fn_ptr(lean::obj __$lean$_$18_140, lean::obj major_premise) {
switch (major_premise.cidx()) {
case 0: {

lean::obj __$lean$_$18_142 = major_premise[0];
lean::obj __$lean$_$18_143 = __$lean$_$18_140;
return __$lean$_$18_143.apply(__$lean$_$18_142);}
default:
lean::runtime_error("recursor-compilation-failure");
break;
}

}

lean::obj prod_cases_on_fn_ptr(lean::obj __$lean$_$18_78, lean::obj __$lean$_$18_79) {
lean::obj __$lean$_$18_87 = lean::mk_closure(__$lean$_$_$closure$_18_83_fn_ptr,1,{__$lean$_$18_79});
lean::obj __$lean$_$18_82 = __$lean$_$18_87;
return prod_rec_fn_ptr(__$lean$_$18_82, __$lean$_$18_78);
}

lean::obj print_line_fn_ptr(lean::obj __$lean$_$18_98, lean::obj __$lean$_$18_99) {
    std::cout << "print_line_fn_ptr" << std::endl;
    lean::obj __$lean$_$18_100 = ToString_to_string.apply(__$lean$_$18_98, __$lean$_$18_99);
    return print_string.apply(__$lean$_$18_100);
}

lean::obj IO_runIO_fn_ptr(lean::obj __$lean$_$18_102) {
lean::obj __$lean$_$18_109 = lean::mk_closure(__$lean$_$_$closure$_18_107_fn_ptr,0,{});
lean::obj __$lean$_$18_106 = __$lean$_$18_109;
return IO_rec_fn_ptr(__$lean$_$18_106, __$lean$_$18_102);
}

lean::obj IO_rec_fn_ptr(lean::obj __$lean$_$18_112, lean::obj major_premise) {
switch (major_premise.cidx()) {
case 0: {

lean::obj __$lean$_$18_114 = major_premise[0];
lean::obj __$lean$_$18_115 = __$lean$_$18_112;
return __$lean$_$18_115.apply(__$lean$_$18_114);}
default:
lean::runtime_error("recursor-compilation-failure");
break;
}

}

lean::obj print_string_fn_ptr(lean::obj __$lean$_$18_116) {
    std::cout << "print_string_fn_ptr" << std::endl;
    lean::obj __$lean$_$18_122 = lean::mk_closure(__$lean$_$_$closure$_18_120_fn_ptr,1,{__$lean$_$18_116});
    lean::obj __$lean$_$18_119 = __$lean$_$18_122;
    lean::obj __$lean$_$18_118 = IO_mk_fn_ptr(__$lean$_$18_119);
    return bind.apply(__$lean$_$18_118, raw_print_io);
}

lean::obj __$lean$_$_$closure$_18_83_fn_ptr(lean::obj __$lean$_$18_79, lean::obj __$lean$_$18_84, lean::obj __$lean$_$18_85) {
lean::obj __$lean$_$18_86 = __$lean$_$18_79;
return __$lean$_$18_86.apply(__$lean$_$18_84, __$lean$_$18_85);
}

lean::obj __$lean$_$_$closure$_18_107_fn_ptr(lean::obj __$lean$_$18_108) {
return __$lean$_$18_108;
}

lean::obj __$lean$_$_$closure$_18_155_fn_ptr(lean::obj __$lean$_$18_146, lean::obj __$lean$_$18_147, lean::obj __$lean$_$18_156) {
lean::obj __$lean$_$18_157 = IO_runIO.apply(__$lean$_$18_146, __$lean$_$18_156);
lean::obj __$lean$_$18_164 = lean::mk_closure(__$lean$_$_$closure$_18_159_fn_ptr,1,{__$lean$_$18_147});
lean::obj __$lean$_$18_158 = __$lean$_$18_164;
return prod_cases_on.apply(__$lean$_$18_157, __$lean$_$18_158);
}

lean::obj __$lean$_$_$closure$_18_120_fn_ptr(lean::obj __$lean$_$18_116, lean::obj __$lean$_$18_121) {
return string_to_raw_string_fn_ptr(__$lean$_$18_121, __$lean$_$18_116);
}

lean::obj __$lean$_$_$closure$_18_159_fn_ptr(lean::obj __$lean$_$18_147, lean::obj __$lean$_$18_160, lean::obj __$lean$_$18_161) {
lean::obj __$lean$_$18_163 = __$lean$_$18_147;
lean::obj __$lean$_$18_162 = __$lean$_$18_163.apply(__$lean$_$18_161);
return IO_runIO.apply(__$lean$_$18_162, __$lean$_$18_160);
}

lean::obj __$lean$_$_$closure$_18_126_fn_ptr(lean::obj __$lean$_$18_123, lean::obj __$lean$_$18_127) {
return raw_print_fn_ptr(__$lean$_$18_127, __$lean$_$18_123);
}

lean::obj __$lean$_$_$closure$_18_135_fn_ptr(lean::obj __$lean$_$18_136) {
return __$lean$_$18_136;
}

lean::obj raw_print_io_fn_ptr(lean::obj __$lean$_$18_123) {
lean::obj __$lean$_$18_128 = lean::mk_closure(__$lean$_$_$closure$_18_126_fn_ptr,1,{__$lean$_$18_123});
lean::obj __$lean$_$18_125 = __$lean$_$18_128;
return IO_mk_fn_ptr(__$lean$_$18_125);
}

lean::obj ToString_to_string_fn_ptr(lean::obj __$lean$_$18_130) {
lean::obj __$lean$_$18_137 = lean::mk_closure(__$lean$_$_$closure$_18_135_fn_ptr,0,{});
lean::obj __$lean$_$18_134 = __$lean$_$18_137;
return ToString_rec_fn_ptr(__$lean$_$18_134, __$lean$_$18_130);
}

lean::obj prod_rec_fn_ptr(lean::obj __$lean$_$18_91, lean::obj major_premise) {
switch (major_premise.cidx()) {
case 0: {

lean::obj __$lean$_$18_94 = major_premise[0];
lean::obj __$lean$_$18_95 = major_premise[1];
lean::obj __$lean$_$18_96 = __$lean$_$18_91;
return __$lean$_$18_96.apply(__$lean$_$18_94, __$lean$_$18_95);}
default:
lean::runtime_error("recursor-compilation-failure");
break;
}

}

lean::obj bind_fn_ptr(lean::obj __$lean$_$18_146, lean::obj __$lean$_$18_147) {
lean::obj __$lean$_$18_165 = lean::mk_closure(__$lean$_$_$closure$_18_155_fn_ptr,2,{__$lean$_$18_146,__$lean$_$18_147});
lean::obj __$lean$_$18_154 = __$lean$_$18_165;
return IO_mk_fn_ptr(__$lean$_$18_154);
}

int main() {
lean::run_lean_main(___lean__main_fn_ptr);
return 0;
}
