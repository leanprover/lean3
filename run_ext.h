#include "lean_runtime.h"

// Take the inductive type that Lean uses to represent a character
// and convert it to a raw character.
char lean_char_to_raw_char(lean::obj c) {
    char r = (c[0].cidx() << 7) |
             (c[1].cidx() << 6) |
             (c[2].cidx() << 5) |
             (c[3].cidx() << 4) |
             (c[4].cidx() << 3) |
             (c[5].cidx()<< 2) |
             (c[6].cidx() << 1) |
             (c[7].cidx());
    return r;
}

// Take the inductive type that Lean uses to represent a string
// and convert it to a raw character.
lean::obj string_to_raw_string_fn_ptr(lean::obj rw, lean::obj string) {
    std::cout << "string to raw string" << string.cidx() << std::endl;
    std::string *raw_string = new std::string("");
    auto cursor = string;
    while (cursor.cidx() == 1) {
        *raw_string += lean_char_to_raw_char(cursor[0]);
        cursor = cursor[1];
    }
    auto rs = lean::mk_raw_ptr((void*)raw_string->c_str());
    return lean::mk_obj(0, { rw, rs });
}

lean::obj raw_print_fn_ptr(lean::obj rw, lean::obj rs) {
    std::cout << "raw_print_fn_ptr" << std::endl;
    auto unit = lean::mk_obj(0);
    std::cout << "raw_ptr" << std::endl;
    auto ptr = (char *)rs.raw_ptr();
    std::cout << ptr;
    return lean::mk_obj(0, { rw, unit });
}

static lean::obj raw_print = mk_closure(raw_print_fn_ptr, 2, 0, nullptr);

// Take the inductive type that Lean uses to represent a string
// and convert it to a raw character.
lean::obj trace_fn_ptr(lean::obj msg, lean::obj result) {
    std::string *raw_string = new std::string("");
    auto cursor = msg;
    while (cursor.cidx() == 1) {
        *raw_string += lean_char_to_raw_char(cursor[0]);
        cursor = cursor[1];
    }
    std::cout << "trace: " << *raw_string << std::endl;
    return result;
}

static lean::obj trace = mk_closure(trace_fn_ptr, 2, 0, nullptr);

size_t nat_to_size_t(lean::obj nat) {
    size_t i = 0;
    auto cursor = nat;
    while (cursor.cidx() == 1) {
        i += 1;
        cursor = cursor[0];
    }
    return i;
}

lean::obj raw_allocate_fn_ptr(lean::obj rw, lean::obj size, lean::obj destructor) {
    auto sz = nat_to_size_t(size);
    auto ptr = lean::mk_raw_ptr(malloc(sz));
    return lean::mk_obj(0, { rw, ptr });
}

static lean::obj raw_allocate = mk_closure(raw_allocate_fn_ptr, 3, {});

lean::obj raw_get_line_fn_ptr(lean::obj rw) {
    std::string *line = new std::string("");
    getline(std::cin, *line);
    auto rs = lean::mk_raw_ptr((void*)line->c_str());
    return lean::mk_obj(0, { rw, rs });
}

static lean::obj raw_get_line = mk_closure(raw_get_line_fn_ptr, 1, {});

lean::obj raw_forever_fn_ptr(lean::obj rw, lean::obj io_action) {
    auto inner_fn = io_action[0];
    auto pair = inner_fn.apply(rw);
    return raw_forever_fn_ptr(pair[0], io_action);
}

static lean::obj raw_forever = mk_closure(raw_forever_fn_ptr, 1, {});
