/*
Author: James King <james@agenultra.com>
*/

#include <dlfcn.h>
#include <ffi/ffi.h>
#include <string>
#include <iostream>
#include <sys/types.h>

#include "util/lean_path.h"

// #include "util/sstream.h"
// #include "library/vm/vm_name.h"
// #include "library/vm/vm_io.h"
// #include "library/vm/vm_string.h"
#include "library/vm/vm_dynload.h"
// #include "library/attribute_manager.h"

#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/attribute_manager.h"
#include "library/scoped_ext.h"
#include "library/tactic/elaborator_exception.h"
#include "library/string.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_parser.h"
#include "library/quote.h"
#include "library/placeholder.h"


// void get_shared_funcptr(string const & pathname) {
//     void* handle = dlopen(pathname.c_str(), RTLD_LAZY);
//     if (!handle) {
//         std::cerr << "Cannot load library: " << dlerror() << '\n';
//     }
// }

namespace lean {
using namespace std;

    ffi_type * to_ffi_type (expr const & e) {
        if (is_constant(e, name("unsigned"))) {
            return &ffi_type_uint32;
        } else {
            throw exception(sstream() << "unsupported ffi type: " << e);
        }
    }

    vm_decl vm_foreign_obj_cell::get_cfun(name const & n, unsigned idx, string const & fun_name,
                                          buffer<expr> const & _args, expr const & _rt) {
        vm_cfunction fn = reinterpret_cast<vm_cfunction>(dlsym(m_handle, fun_name.c_str()));
        if (!fn) {
            auto err = dlerror();
            throw exception(err); }
        buffer<ffi_type *> args;
        for (auto e : _args) { args.push_back(to_ffi_type(e)); }
        ffi_type * rt = to_ffi_type(_rt);
        auto_ptr<vm_cfun_sig> sig(new vm_cfun_sig(FFI_DEFAULT_ABI, *rt, std::move(args)));
        return vm_decl(n, idx, sig, fn);
    }

    vm_foreign_obj_cell::~vm_foreign_obj_cell() {
        dlclose(m_handle);
    }

    void vm_foreign_obj_cell::dealloc() {
        delete this;
    }

    vm_foreign_obj::vm_foreign_obj(string const & fname) {
        auto root = get_leanpkg_path_file();
        push_dir _(root ? dirname(*root) : lgetcwd());
        FOREIGN_OBJ handle = dlopen(fname.c_str(), RTLD_LAZY);
        if (!handle) {
            throw exception(sstream() << "failed to load foreign lib: " << dlerror() << "\n" << root->c_str());
        }
        m_ptr = new vm_foreign_obj_cell(handle, fname);
        m_ptr->inc_ref();
    }

    static name * g_vm_ffi;
    struct vm_ffi_attribute_data : public attr_data {
        name m_obj;
        optional<name> m_c_fun;
        vm_ffi_attribute_data() {}
        vm_ffi_attribute_data(name const & obj, optional<name> const & fn) :
            m_obj(obj), m_c_fun(fn) {}
        virtual unsigned hash() const override {return m_obj.hash();}
        void write(serializer & s) const {s << m_obj << m_c_fun;}
        void read(deserializer & d) {
            d >> m_obj >> m_c_fun;
        }
        void parse(abstract_parser & p) override {
            lean_assert(dynamic_cast<parser *>(&p));
            auto & p2 = *static_cast<parser *>(&p);
            auto n = p2.check_id_next("not an identifier");
            m_obj = n;
            if (p2.curr_is_identifier()) {
                m_c_fun = optional<name>(p2.get_name_val());
                p2.next();
            } else {
                m_c_fun = optional<name>();
            }
        }
    };
    bool operator==(vm_ffi_attribute_data const & d1, vm_ffi_attribute_data const & d2) {
        return d1.m_obj == d2.m_obj &&
            d1.m_c_fun == d2.m_c_fun;
    }

    template class typed_attribute<vm_ffi_attribute_data>;
    typedef typed_attribute<vm_ffi_attribute_data> vm_ffi_attribute;

    static vm_ffi_attribute const & get_vm_ffi_attribute() {
        return static_cast<vm_ffi_attribute const &>(get_system_attribute(*g_vm_ffi));
    }


    void initialize_vm_ffi() {
        g_vm_ffi = new name("ffi");
        register_system_attribute(vm_ffi_attribute(
            *g_vm_ffi, "Registers a binding to a foreign function.",
            [](environment const & env, io_state const &, name const & d, unsigned, bool) -> environment {
                auto data = get_vm_ffi_attribute().get(env, d);
                name sym = data->m_c_fun? *data->m_c_fun : d;
                auto b = add_foreign_symbol(env, data->m_obj, d, sym.to_string());
                return b;
            }));
    }

    void finalize_vm_ffi() {
        delete g_vm_ffi;
    }

    static name * g_vm_ffi;
    struct vm_ffi_attribute_data : public attr_data {
        name m_obj;
        optional<name> m_c_fun;
        vm_ffi_attribute_data() {}
        // vm_ffi_attribute_data(name const & n) : m_name(n) {}
        // virtual unsigned hash() const override {return m_name.hash();}
        void write(serializer & s) const {s << m_obj << m_c_fun;}
        void read(deserializer & d) {
            d >> m_obj >> m_c_fun;
        }
        void parse(abstract_parser & p) override {
            lean_assert(dynamic_cast<parser *>(&p));
            auto & p2 = *static_cast<parser *>(&p);
            m_obj = p2.check_constant_next("not a constant");
            if (p2.curr_is_identifier()) {
                m_c_fun = optional<name>(p2.get_name_val());
                p2.next();
            } else {
                m_c_fun = optional<name>();
            }
        }
    };
    // bool operator==(vm_ffi_attribute_data const & d1, vm_ffi_attribute_data const & d2) {
    //     return d1.m_name == d2.m_name;
    // }

    template class typed_attribute<vm_ffi_attribute_data>;
    typedef typed_attribute<vm_ffi_attribute_data> vm_ffi_attribute;

    static vm_ffi_attribute const & get_vm_ffi_attribute() {
        return static_cast<vm_ffi_attribute const &>(get_system_attribute(*g_vm_ffi));
    }


    void initialize_vm_ffi() {
        register_system_attribute(basic_attribute(
            "ffi", "Registers a binding to a foreign function.",
            [](environment const & env, io_state const &, name const & d, unsigned, bool) -> environment {
                auto data = get_vm_ffi_attribute().get(env, d);
                name sym = data->m_c_fun? *data->m_c_fun : data->m_obj;
                return add_foreign_symbol(env, d, data->m_obj, sym.to_string());
            }));
    }

    void finalize_vm_ffi() {
    }

}
