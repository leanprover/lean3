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
#include "library/process.h"
#include "unistd.h"
#include "stdio.h"

namespace lean {

vm_obj process_pipe_write(vm_obj const &, vm_obj const & pipe_obj, vm_obj const & array_obj, vm_obj const &) {
    handle_ref handle = to_handle(pipe_obj);
    auto arr = to_array(array_obj);
    throw exception("yolo");
    // /* Fix this code, perf is bad, but crashed for some reason */
    // std::string buf;
    // for (size_t i = 0; i < arr.size(); i++) {
    //     buf += (char)cidx(arr[i]);
    // }

    // write(pipe_fd, buf.c_str(), buf.size());
    // close(pipe_fd);
    return mk_io_result(mk_vm_unit());
}

vm_obj process_pipe_read(vm_obj const &, vm_obj const & pipe_obj, vm_obj const & array_obj, vm_obj const &) {
    handle_ref handle = to_handle(pipe_obj);
    auto arr = to_array(array_obj);

    throw exception("yolo");
    // buffer<char> buf;
    // buf.resize(arr.size());

    int bytes_read = 0;
    // int bytes_read = read(pipe_fd, buf.data(), buf.size());

    // if (bytes_read == -1) {
    //     // TODO
    //     throw exception("pipe read failed");
    // }

    // for (size_t i = 0; i < buf.size(); i++) {
    //    arr.set(i, mk_vm_nat(buf[i]));
    // }

    return mk_io_result(mk_vm_pair(mk_vm_nat(bytes_read), to_obj(arr)));
}

void initialize_vm_process() {
}

void finalize_vm_process() {
}
}
