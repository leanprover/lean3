/*
Copyright (c) 2019 James King. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: James King <james@agenultra.com>, Simon Hudon
*/

#include <dlfcn.h>
#ifdef __linux__
  #include <ffi.h>
#else
  #include <ffi/ffi.h>
#endif
#include <string>

#include "util/lean_path.h"
#include "library/vm/vm_ffi.h"
#include "library/vm/vm_parser.h"

namespace lean {

    static name * g_vm_ffi;

    // types
    static name * g_uint8_name;
    static name * g_uint16_name;
    static name * g_uint32_name;
    static name * g_uint64_name;
    static name * g_int8_name;
    static name * g_int16_name;
    static name * g_int32_name;
    static name * g_int64_name;

    ffi_type * to_ffi_type (expr const & e) {
        if (is_constant(e, *g_uint8_name)) {
            return &ffi_type_uint8;
        } else if (is_constant(e, *g_uint16_name)) {
            return &ffi_type_uint16;
        } else if (is_constant(e, *g_uint32_name)) {
            return &ffi_type_uint32;
        } else if (is_constant(e, *g_uint64_name)) {
            return &ffi_type_uint64;
        } else if (is_constant(e, *g_int8_name)) {
            return &ffi_type_sint8;
        } else if (is_constant(e, *g_int16_name)) {
            return &ffi_type_sint16;
        } else if (is_constant(e, *g_int32_name)) {
            return &ffi_type_sint32;
        } else if (is_constant(e, *g_int64_name)) {
            return &ffi_type_sint64;
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
        unique_ptr<vm_cfun_sig> sig(new vm_cfun_sig(FFI_DEFAULT_ABI, *rt, std::move(args)));
        return vm_decl(n, idx, std::move(sig), fn);
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
        vm_foreign_obj_cell::handle_t handle = dlopen(fname.c_str(), RTLD_LAZY);
        if (!handle) {
            throw exception(sstream() << "failed to load foreign lib: " << dlerror());
        }
        m_ptr = new vm_foreign_obj_cell(handle, fname);
        m_ptr->inc_ref();
    }

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
        g_uint8_name  = new name ({"foreign", "uint_8"});
        g_uint16_name = new name ({"foreign", "uint_16"});
        g_uint32_name = new name ({"foreign", "uint_32"});
        g_uint64_name = new name ({"foreign", "uint_64"});
        g_int8_name   = new name ({"foreign", "int_8"});
        g_int16_name  = new name ({"foreign", "int_16"});
        g_int32_name  = new name ({"foreign", "int_32"});
        g_int64_name  = new name ({"foreign", "int_64"});

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
        delete g_uint8_name;
        delete g_uint16_name;
        delete g_uint32_name;
        delete g_uint64_name;
        delete g_int8_name;
        delete g_int16_name;
        delete g_int32_name;
        delete g_int64_name;
    }

}
