/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <iostream>
#include "library/io_state.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_array.h"
#include "util/process.h"
#include "unistd.h"

namespace lean {

struct vm_process : public vm_external {
    process m_val;
    vm_process(process v):m_val(v) {}
    virtual ~vm_process() {}
    virtual void dealloc() override {
        this->~vm_process();
        get_vm_allocator().deallocate(sizeof(vm_process), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {
        return new vm_process(m_val);
    }

    virtual vm_external * clone(vm_clone_fn const &) override {
        return new (get_vm_allocator().allocate(sizeof(vm_process))) vm_process(m_val);
    }
};

bool is_process(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_process*>(to_external(o));
}

process & to_process(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_process*>(to_external(o)));
    return static_cast<vm_process*>(to_external(o))->m_val;
}

vm_obj to_obj(vm_process const & e) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_process))) vm_process(e));
}

struct vm_stdio : public vm_external {
    stdio m_val;
    vm_stdio(stdio v):m_val(v) {}
    virtual ~vm_stdio() {}
    virtual void dealloc() override {
        this->~vm_stdio();
        get_vm_allocator().deallocate(sizeof(vm_stdio), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {
        return new vm_stdio(m_val);
    }

    virtual vm_external * clone(vm_clone_fn const &) override {
        return new (get_vm_allocator().allocate(sizeof(vm_stdio))) vm_stdio(m_val);
    }
};

bool is_stdio(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_stdio*>(to_external(o));
}

stdio & to_stdio(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_stdio*>(to_external(o)));
    return static_cast<vm_stdio*>(to_external(o))->m_val;
}

vm_obj to_obj(vm_stdio const & e) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_stdio))) vm_stdio(e));
}

stdio from_obj(vm_obj const & o) {
    switch(cidx(o)) {
        case 0:
            return stdio::PIPED;
        case 1:
            return stdio::INHERIT;
        case 2:
            return stdio::NUL;
    }
}

struct vm_child : public vm_external {
    child m_val;
    vm_child(child v):m_val(v) {}
    virtual ~vm_child() {}
    virtual void dealloc() override {
        this->~vm_child();
        get_vm_allocator().deallocate(sizeof(vm_child), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {
        return new vm_child(m_val);
    }

    virtual vm_external * clone(vm_clone_fn const &) override {
        return new (get_vm_allocator().allocate(sizeof(vm_child))) vm_child(m_val);
    }
};

bool is_child(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_child*>(to_external(o));
}

child & to_child(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_child*>(to_external(o)));
    return static_cast<vm_child*>(to_external(o))->m_val;
}

vm_obj to_obj(vm_child const & e) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_child))) vm_child(e));
}

struct vm_pipe : public vm_external {
    int m_val;
    vm_pipe(int v):m_val(v) {}
    virtual ~vm_pipe() {}
    virtual void dealloc() override {
        this->~vm_pipe();
        get_vm_allocator().deallocate(sizeof(vm_pipe), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {
        return new vm_pipe(m_val);
    }

    virtual vm_external * clone(vm_clone_fn const &) override {
        return new (get_vm_allocator().allocate(sizeof(vm_pipe))) vm_pipe(m_val);
    }
};

bool is_pipe(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_pipe*>(to_external(o));
}

int to_pipe(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_pipe*>(to_external(o)));
    return static_cast<vm_pipe*>(to_external(o))->m_val;
}

vm_obj to_obj(vm_pipe const & e) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_pipe))) vm_pipe(e));
}

vm_obj process_builder_new(vm_obj const & string_obj, vm_obj const &) {
    auto command = to_string(string_obj);
    process proc = process(command);
    return mk_io_result(to_obj(proc));
}

vm_obj process_builder_spawn(vm_obj const & builder_obj, vm_obj const &) {
    process & builder = to_process(builder_obj);
    child ch = builder.spawn();
    // Should add helper functions for building real io.result
    return mk_io_result(to_obj(ch));
}

vm_obj process_builder_arg(vm_obj const & builder_obj, vm_obj const & arg_obj, vm_obj const &) {
    process & proc = to_process(builder_obj);
    auto arg = to_string(arg_obj);
    proc.arg(arg);
    return mk_io_result(mk_vm_unit());
}

vm_obj process_builder_stdin(vm_obj const & builder_obj, vm_obj const & stdio_obj, vm_obj const &) {
    process & proc = to_process(builder_obj);
    auto cfg = from_obj(stdio_obj);
    proc.stdin(cfg);
    return mk_io_result(mk_vm_unit());
}

vm_obj process_builder_stdout(vm_obj const & builder_obj, vm_obj const & stdio_obj, vm_obj const &) {
    process & proc = to_process(builder_obj);
    auto cfg = from_obj(stdio_obj);
    proc.stdout(cfg);
    return mk_io_result(mk_vm_unit());
}

vm_obj process_builder_stderr(vm_obj const & builder_obj, vm_obj const & stdio_obj, vm_obj const &) {
    process & proc = to_process(builder_obj);
    auto cfg = from_obj(stdio_obj);
    proc.stderr(cfg);
    return mk_io_result(mk_vm_unit());
}

vm_obj process_child_stdin(vm_obj const & child_obj, vm_obj const &) {
    auto child = to_child(child_obj);
    return mk_io_result(to_obj(vm_pipe(child.m_stdin)));
}

vm_obj process_child_stdout(vm_obj const & child_obj, vm_obj const &) {
    auto child = to_child(child_obj);
    return mk_io_result(to_obj(vm_pipe(child.m_stdout)));
}

vm_obj process_child_stderr(vm_obj const & child_obj, vm_obj const &) {
    auto child = to_child(child_obj);
    return mk_io_result(to_obj(vm_pipe(child.m_stderr)));
}

vm_obj process_pipe_write(vm_obj const &, vm_obj const & pipe_obj, vm_obj const & array_obj, vm_obj const &) {
    auto pipe_fd = to_pipe(pipe_obj);
    std::cout << "in pipe write " << pipe_fd << std::endl;
    auto arr = to_array(array_obj);

    /* Fix this code, perf is bad, but crashed for some reason */
    std::string buf;
    for (size_t i = 0; i < arr.size(); i++) {
        buf += (char)cidx(arr[i]);
    }

    write(pipe_fd, buf.c_str(), buf.size());
    close(pipe_fd);
    return mk_io_result(mk_vm_unit());
}

vm_obj process_pipe_read(vm_obj const &, vm_obj const & pipe_obj, vm_obj const & array_obj, vm_obj const &) {
    auto pipe_fd = to_pipe(pipe_obj);
    std::cout << "in pipe read" << pipe_fd << std::endl;
    auto arr = to_array(array_obj);

    buffer<char> buf;
    buf.resize(arr.size());

    int bytes_read = read(pipe_fd, buf.data(), buf.size());

    if (bytes_read == -1) {
        // TODO
        throw exception("pipe read failed");
    }

    return mk_io_result(mk_vm_nat(bytes_read));
}

void initialize_vm_process() {
    DECLARE_VM_BUILTIN(name({"process", "builder", "new"}),     process_builder_new);
    DECLARE_VM_BUILTIN(name({"process", "builder", "spawn"}),   process_builder_spawn);
    DECLARE_VM_BUILTIN(name({"process", "builder", "arg"}),     process_builder_arg);
    DECLARE_VM_BUILTIN(name({"process", "builder", "stdin"}),   process_builder_stdin);
    DECLARE_VM_BUILTIN(name({"process", "builder", "stdout"}),  process_builder_stdout);
    DECLARE_VM_BUILTIN(name({"process", "builder", "stderr"}),  process_builder_stderr);
    DECLARE_VM_BUILTIN(name({"process", "child", "stdin"}),     process_child_stdin);
    DECLARE_VM_BUILTIN(name({"process", "child", "stdout"}),    process_child_stdout);
    DECLARE_VM_BUILTIN(name({"process", "child", "stderr"}),    process_child_stderr);
    DECLARE_VM_BUILTIN(name({"process", "pipe", "write"}),      process_pipe_write);
    DECLARE_VM_BUILTIN(name({"process", "pipe", "read"}),       process_pipe_read);
}

void finalize_vm_process() {
}
}
