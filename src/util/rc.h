/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

// Goodies for reference counting
#include "util/thread.h"
#include "util/debug.h"

#define MK_LEAN_RC()                                                    \
private:                                                                \
atomic<unsigned> m_rc;                                                  \
public:                                                                 \
unsigned get_rc() const { return atomic_load(&m_rc); }                  \
void inc_ref() { atomic_fetch_add_explicit(&m_rc, 1u, memory_order_relaxed); } \
bool dec_ref_core() {                                                   \
    lean_assert(get_rc() > 0);                                          \
    if (atomic_fetch_sub_explicit(&m_rc, 1u, memory_order_release) == 1u) { \
        atomic_thread_fence(memory_order_acquire);                      \
        return true;                                                    \
    } else {                                                            \
        return false;                                                   \
    }                                                                   \
}                                                                       \
void dec_ref() { if (dec_ref_core()) { dealloc(); } }

#define LEAN_COPY_REF(Arg)                      \
    if (Arg.m_ptr)                              \
        Arg.m_ptr->inc_ref();                   \
    auto new_ptr = Arg.m_ptr;                   \
    if (m_ptr)                                  \
        m_ptr->dec_ref();                       \
    m_ptr = new_ptr;                            \
    return *this;

#define LEAN_MOVE_REF(Arg)                      \
    if (m_ptr)                                  \
        m_ptr->dec_ref();                       \
    m_ptr   = Arg.m_ptr;                        \
    Arg.m_ptr = nullptr;                        \
    return *this;

namespace lean {
template <class T>
class arc {
    struct impl {
        T m_value;
        MK_LEAN_RC();
        void dealloc() { delete this; }

        impl(T const & t) : m_rc(0), m_value(t) {}
        impl(T && t) : m_rc(0), m_value(t) {}
    };

    impl * m_ptr = nullptr;

    arc(impl * ptr) : m_ptr(ptr) { if (ptr) ptr->inc_ref(); }

public:
    arc(T const & t) : arc(new impl(t)) {}
    arc(T && t) : arc(new impl(t)) {}
    arc(arc<T> const & a) : arc(a.m_ptr) {}
    arc(arc<T> && a) : m_ptr(a.m_ptr) { a.m_ptr = nullptr; }
    ~arc() { if (m_ptr) m_ptr->dec_ref(); }

    arc<T> & operator=(arc<T> const & t) { LEAN_COPY_REF(t); }
    arc<T> & operator=(arc<T> && t) { LEAN_MOVE_REF(t); }

    T * operator->() const { return get(); }
    T & operator*() const { return *get(); }

    bool operator==(arc<T> const & that) const { return m_ptr == that.m_ptr; }
    bool operator!=(arc<T> const & that) const { return m_ptr != that.m_ptr; }

    T * get() const { return &m_ptr->m_value; }

    operator bool() const { return m_ptr != nullptr; }
};
}
