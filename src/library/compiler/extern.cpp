/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "library/trace.h"
#include "library/scoped_ext.h"
#include "library/extern.h"
#include "library/attribute_manager.h"

namespace lean {
    /* The environment extension */
    static name * g_class_name = nullptr;
    static std::string * g_key = nullptr;

    struct extern_entry {
        extern_status  m_status;
        name           m_name;
        extern_entry():m_status(extern_status::NotExternal) {}
        extern_entry(extern_status s, name const & n):m_status(s), m_name(n) {}
    };

    typedef name_map<extern_status> extern_state;

    static extern_status get_status(extern_state const & s, name const & n) {
        if (auto it = s.find(n))
            return *it;
        else
            return extern_status::NotExternal;
    }

    static name * g_class_name = nullptr;
    static std::string * g_key = nullptr;

    struct extern_config {
        typedef extern_state  state;
        typedef extern_entry  entry;
        static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
            s.insert(e.m_name, e.m_status);
        }
        static name const & get_class_name() {
             return *g_class_name;
        }
        static std::string const & get_serialization_key() {
            return *g_key;
        }
        static void  write_entry(serializer & s, entry const & e) {
            s << static_cast<char>(e.m_status) << e.m_name;
        }
        static entry read_entry(deserializer & d) {
            entry e; char s;
            d >> s >> e.m_name;
            e.m_status = static_cast<extern_status>(s);
            return e;
        }
        static optional<unsigned> get_fingerprint(entry const & e) {
            return some(hash(static_cast<unsigned>(e.m_status), e.m_name.hash()));
        }
    };

    typedef scoped_ext<extern_config> extern_ext;
    typedef scoped_ext<extern_config> extern_ext;

    void initialize_simp_lemmas() {
        g_class_name    = new name("simp");
        g_key           = new std::string("SIMP");
        simp_ext::initialize();

        register_prio_attribute("simp", "simplification lemma",
                                add_simp_lemma,
                                is_simp_lemma,
                                [](environment const & env, name const & d) {
                                    if (auto p = simp_ext::get_state(env).m_simp_lemmas.get_prio(d))
                                        return *p;
                                    else
                                        return LEAN_DEFAULT_PRIORITY;
                                });

        register_prio_attribute("congr", "congruence lemma",
                                add_congr_lemma,
                                is_congr_lemma,
                                [](environment const & env, name const & d) {
                                    if (auto p = simp_ext::get_state(env).m_congr_lemmas.get_prio(d))
                                        return *p;
                                    else
                                        return LEAN_DEFAULT_PRIORITY;
                                });
    }

    void initialize_extern() {
        g_class_name = new name("extern");
        g_key        = new std::string("EXTERN");
        extern_ext::initialize();

        register_attribute("extern", "external function",
                           [](environment const & env, io_state const &, name const & d, name const & ns, bool persistent) {
                               return set_extern(env, d, extern_status::External, ns, persistent);
                           },
                           [](environment const & env, name const & d) {
                               return get_extern_status(env, d) == extern_status::External;
                           });
    }

    void finalize_extern() {
        extern_ext::finalize();
        delete g_key;
        delete g_class_name;
    }

    void for_each_extern(environment const & env, std::function<void(name const &, extern_status)> const & fn) {
        extern_state m_state = extern_ext::get_state(env);
        m_state.for_each(fn);
    }

    environment set_extern(environment const & env, name const & n, extern_status s, name const & ns, bool persistent) {
        return extern_ext::add_entry(env, get_dummy_ios(), extern_entry(s, n), ns, persistent);
    }

    extern_status get_extern_status(environment const & env, name const & n) {
        extern_state const & s = extern_ext::get_state(env);
        return get_status(s, n);
    }

    // name_predicate mk_not_extern_pred(environment const & env) {
    //     extern_state m_state = extern_ext::get_state(env);
    //     return [=](name const & n) { // NOLINT
    //         return get_status(m_state, n) != extern_status::External;
    //     };
    // }
    }
}
