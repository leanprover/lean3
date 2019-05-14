/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <chrono>
#include <thread>
#include <sys/types.h>
#include <sys/stat.h>
#ifdef _MSC_VER
    #include <io.h>
    #include <direct.h>
    #define getcwd _getcwd
    #define stat _stat
    #define access _access
    #define PATH_MAX _MAX_PATH

    #define S_IFMT  _S_IFMT
    #define S_IFREG _S_IFREG
    #define S_IFDIR _S_IFDIR
#else
    #include <unistd.h>
#endif
#if defined(__linux__) || defined(__APPLE__)
    #include <sys/socket.h>
    #include <sys/un.h>
    #define SOCKET int
    #define SOCKIO_BYTES ssize_t
    #define INVALID_SOCKET (-1)
    #define SOCKET_ERROR (-1)
    #define SOCKET_GET_ERROR() strerror(errno)
    #define closesocket(fd) close(fd)
#else
    #ifndef NOMINMAX
        #define NOMINMAX
    #endif
    #include <Winsock2.h>
    #include <windows.h>
    #include <Fileapi.h>
    #define UNIX_PATH_MAX 108

    typedef struct sockaddr_un {
        ADDRESS_FAMILY sun_family;
        char sun_path[UNIX_PATH_MAX];
    } SOCKADDR_UN, *PSOCKADDR_UN;

    #define SOCKIO_BYTES int
    #define SOCKET_GET_ERROR() WSAGetLastError()
#endif
#ifdef __linux__
    #include <linux/limits.h>
#endif
#include <util/unit.h>
#include "util/sstream.h"
#include "util/utf8.h"
#include "util/path.h"
#include "library/handle.h"
#include "library/io_state.h"
#include "library/constants.h"
#include "library/process.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_array.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/kernel_serializer.h"

namespace lean {
vm_obj io_core(vm_obj const &, vm_obj const &) {
    return mk_vm_unit();
}

vm_obj mk_io_result(vm_obj const & r) {
    return mk_vm_constructor(0, 1, &r);
}

vm_obj mk_io_failure(vm_obj const & e) {
    return mk_vm_constructor(1, 1, &e);
}

vm_obj mk_io_failure(std::string const & s) {
    return mk_io_failure(mk_vm_constructor(0, to_obj(s)));
}

vm_obj mk_io_failure(sstream const & s) {
    return mk_io_failure(mk_vm_constructor(0, to_obj(s.str())));
}

static vm_obj io_put_str(vm_obj const & str, vm_obj const &) {
    get_global_ios().get_regular_stream() << to_string(str);
    return mk_io_result(mk_vm_unit());
}

static vm_obj io_get_line(vm_obj const &) {
    if (get_global_ios().get_options().get_bool("server"))
        throw exception("get_line: cannot read from stdin in server mode");
    std::string str;
    std::getline(std::cin, str);
    return mk_io_result(to_obj(str));
}

static vm_obj cmdline_args_to_obj(std::vector<std::string> const & ss) {
    buffer<vm_obj> objs;
    for (auto & s : ss) objs.push_back(to_obj(s));
    return to_obj(objs);
}

struct vm_handle : public vm_external {
    handle_ref m_handle;
    vm_handle(handle_ref const & h):m_handle(h) {}
    vm_handle(handle_ref && h):m_handle(std::move(h)) {}
    virtual ~vm_handle() {}
    virtual void dealloc() override { this->~vm_handle(); get_vm_allocator().deallocate(sizeof(vm_handle), this); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_handle(m_handle); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { lean_unreachable(); }
};

static handle_ref const & to_handle(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_handle*>(to_external(o)));
    return static_cast<vm_handle*>(to_external(o))->m_handle;
}

static vm_obj to_obj(handle_ref && h) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_handle))) vm_handle(std::move(h)));
}

struct vm_socket : public vm_external {
    SOCKET m_fd;
    vm_socket(SOCKET fd) : m_fd(fd) {}
    virtual ~vm_socket() {}
    virtual void dealloc() override { this->~vm_socket(); get_vm_allocator().deallocate(sizeof(vm_socket), this); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_socket(m_fd); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { lean_unreachable(); }
};

static SOCKET socket_to_fd(vm_obj const &o) {
    lean_vm_check(dynamic_cast<vm_socket*>(to_external(o)));
    return static_cast<vm_socket*>(to_external(o))->m_fd;
}

static vm_obj mk_socket(SOCKET fd) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_socket))) vm_socket(fd));
}

struct vm_child : public vm_external {
    std::shared_ptr<child> m_child;
    vm_child(std::shared_ptr<child> && h):m_child(std::move(h)) {}
    vm_child(std::shared_ptr<child> const & h):m_child(h) {}
    virtual ~vm_child() {}
    virtual void dealloc() override { this->~vm_child(); get_vm_allocator().deallocate(sizeof(vm_child), this); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_child(m_child); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { lean_unreachable(); }
};

std::shared_ptr<child> const & to_child(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_child*>(to_external(o)));
    return static_cast<vm_child*>(to_external(o))->m_child;
}

static vm_obj to_obj(std::shared_ptr<child> && h) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_child))) vm_child(std::move(h)));
}

/*
inductive io.mode
| read | write | read_write | append
*/
char const * to_c_io_mode(unsigned int mode, bool is_bin) {
    switch (mode) {
    case 0: return is_bin ? "rb" : "r";
    case 1: return is_bin ? "wb" : "w";
    case 2: return is_bin ? "r+b" : "r+";
    case 3: return is_bin ? "ab" : "a";
    }
    lean_vm_check(false);
    lean_unreachable();
}

/* (mk_file_handle : string → io.mode → bool → m io.error handle) */
static vm_obj fs_mk_file_handle(vm_obj const & fname, vm_obj const & m, vm_obj const & bin, vm_obj const &) {
    bool is_bin = to_bool(bin);
    FILE * h = fopen(to_string(fname).c_str(), to_c_io_mode(cidx(m), is_bin));
    if (h != nullptr)
        return mk_io_result(to_obj(std::make_shared<handle>(h, is_bin)));
    else
        return mk_io_failure(sstream() << "failed to open file '" << to_string(fname) << "'");
}

static vm_obj mk_handle_has_been_closed_error() {
    return mk_io_failure("invalid io action, handle has been closed");
}

static vm_obj fs_is_eof(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (href->is_closed()) return mk_handle_has_been_closed_error();
    bool r = feof(href->m_file) != 0;
    return mk_io_result(mk_vm_bool(r));
}

static vm_obj fs_flush(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    try {
        href->flush();
        return mk_io_result(mk_vm_unit());
    } catch (handle_exception e) {
        return mk_io_failure("flush failed");
    }
}

static vm_obj fs_close(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    if (href->is_stdin())
        return mk_io_failure("close failed, stdin cannot be closed");
    if (href->is_stdout())
        return mk_io_failure("close failed, stdout cannot be closed");
    if (href->is_stderr())
        return mk_io_failure("close failed, stderr cannot be closed");

    try {
        href->close();
        return mk_io_result(mk_vm_unit());
    } catch (handle_exception e) {
        return mk_io_failure("close failed");
    }
}

static vm_obj mk_buffer(parray<vm_obj> const & a) {
    return mk_vm_pair(mk_vm_nat(a.size()), to_obj(a));
}

static vm_obj net_listen(vm_obj const & fname, vm_obj const & backlog, vm_obj const &) {
    SOCKET fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd == INVALID_SOCKET) {
        return mk_io_failure(sstream() << "failed to open UNIX socket '" << to_string(fname) << "': " << SOCKET_GET_ERROR());
    }

    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    snprintf(addr.sun_path, sizeof(addr.sun_path), "%s", to_string(fname).c_str());
    int ret = bind(fd, (struct sockaddr*) &addr, sizeof(addr));
    if (ret == SOCKET_ERROR) {
        return mk_io_failure(sstream() << "failed to bind UNIX socket '" << to_string(fname) << "': " << SOCKET_GET_ERROR());
    }

    ret = listen(fd, force_to_unsigned(backlog));
    if (ret == SOCKET_ERROR) {
        return mk_io_failure(sstream() << "failed to listen UNIX socket '" << to_string(fname) << "': " << SOCKET_GET_ERROR());
    }

    return mk_io_result(mk_socket(fd));
}

static vm_obj net_accept(vm_obj const & h, vm_obj const &) {
    SOCKET nfd = accept(socket_to_fd(h), NULL, NULL);
    if (nfd == INVALID_SOCKET) {
        return mk_io_failure(sstream() << "failed to accept UNIX socket '" << "': " << SOCKET_GET_ERROR());
    }

    return mk_io_result(mk_socket(nfd));
}

static vm_obj net_connect(vm_obj const & fname, vm_obj const &) {
    SOCKET fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd == INVALID_SOCKET) {
        return mk_io_failure(sstream() << "failed to open UNIX socket '" << to_string(fname) << "'");
    }

    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    snprintf(addr.sun_path, sizeof(addr.sun_path), "%s", to_string(fname).c_str());
    int ret = connect(fd, (struct sockaddr*) &addr, sizeof(addr));
    if (ret == SOCKET_ERROR) {
        return mk_io_failure(sstream() << "failed to connect UNIX socket '" << to_string(fname) << "': " << SOCKET_GET_ERROR());
    }

    return mk_io_result(mk_socket(fd));
}

static vm_obj net_recv(vm_obj const & h, vm_obj const & n, vm_obj const &) {
    SOCKET fd = socket_to_fd(h);
    buffer<char> tmp;
    unsigned num = force_to_unsigned(n);
    tmp.resize(num, 0);

    SOCKIO_BYTES sz = recv(fd, tmp.data(), num, MSG_WAITALL);
    if (sz == SOCKET_ERROR) {
        return mk_io_failure(sstream() << "recv failed: " << SOCKET_GET_ERROR());
    }

    parray<vm_obj> r;
    for (int i = 0; i < sz; i++) {
        r.push_back(mk_vm_simple(static_cast<unsigned char>(tmp[i])));
    }
    return mk_io_result(mk_buffer(r));
}

static vm_obj net_send(vm_obj const & h, vm_obj const & b, vm_obj const &) {
    SOCKET fd = socket_to_fd(h);
    buffer<char> tmp;
    parray<vm_obj> const & a = to_array(cfield(b, 1));
    unsigned sz = a.size();
    for (unsigned i = 0; i < sz; i++) {
        push_unicode_scalar(tmp, cidx(a[i]));
    }

    SOCKIO_BYTES ret = send(fd, tmp.data(), tmp.size(), 0);
    if (ret == sz) {
        return mk_io_result(mk_vm_unit());
    } else {
        return mk_io_failure(sstream() << "send failed: " << SOCKET_GET_ERROR());
    }
}

static vm_obj net_close(vm_obj const & h, vm_obj const &) {
    closesocket(socket_to_fd(h));
    return mk_io_result(mk_vm_unit());
}

static vm_obj monad_io_net_system_impl () {
    return mk_vm_constructor(0, {
        mk_native_closure(net_listen),
        mk_native_closure(net_accept),
        mk_native_closure(net_connect),
        mk_native_closure(net_recv),
        mk_native_closure(net_send),
        mk_native_closure(net_close)});
}

static vm_obj fs_read(vm_obj const & h, vm_obj const & n, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (href->is_closed()) return mk_handle_has_been_closed_error();
    buffer<char> tmp;
    unsigned num = force_to_unsigned(n); /* TODO(Leo): handle size_t */
    size_t bytes = num * (href->m_binary ? 1 : 4);
    tmp.resize(bytes, 0);
    size_t sz = fread(tmp.data(), 1, bytes, href->m_file);
    if (ferror(href->m_file)) {
        clearerr(href->m_file);
        return mk_io_failure("read failed");
    }
    parray<vm_obj> r;
    if (href->m_binary) {
        for (size_t i = 0; i < sz; i++) {
            r.push_back(mk_vm_simple(static_cast<unsigned char>(tmp[i])));
        }
    } else {
        size_t i = 0;
        for (size_t chars = 0; chars < num && i < sz; chars++) {
            r.push_back(mk_vm_simple(next_utf8_buff(tmp.data(), sz, i)));
        }

        size_t extra = static_cast<size_t>(sz - i);
        if (extra > 0) {
            fseek(href->m_file, -extra, SEEK_CUR);
        }
    }
    return mk_io_result(mk_buffer(r));
}

static vm_obj fs_write(vm_obj const & h, vm_obj const & b, vm_obj const &) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    buffer<char> tmp;
    parray<vm_obj> const & a = to_array(cfield(b, 1));
    unsigned sz = a.size();
    for (unsigned i = 0; i < sz; i++) {
        if (href->m_binary) {
            tmp.push_back(static_cast<unsigned char>(cidx(a[i])));
        } else {
            push_unicode_scalar(tmp, cidx(a[i]));
        }
    }

    try {
        href->write(tmp);
        return mk_io_result(mk_vm_unit());
    } catch (handle_exception e) {
        return mk_io_failure("write failed");
    }
}

static vm_obj fs_get_line(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    parray<vm_obj> r;
    while (true) {
        int c = fgetc(href->m_file);
        if (ferror(href->m_file)) {
            clearerr(href->m_file);
            return mk_io_failure("get_line failed");
        }
        if (c == EOF)
            break;
        r.push_back(mk_vm_simple(static_cast<unsigned char>(static_cast<char>(c))));
        if (c == '\n')
            break;
    }
    return mk_io_result(mk_buffer(r));
}

static vm_obj fs_stdin(vm_obj const &) {
    return mk_io_result(to_obj(std::make_shared<handle>(stdin, false)));
}

static vm_obj fs_stdout(vm_obj const &) {
    return mk_io_result(to_obj(std::make_shared<handle>(stdout, false)));
}

static vm_obj fs_stderr(vm_obj const &) {
    return mk_io_result(to_obj(std::make_shared<handle>(stderr, false)));
}

#define FSTAT_FAIL 0
#define FSTAT_MISC 1
#define FSTAT_FILE 2
#define FSTAT_DIR  3

static int fs_stat(const char *path) {
    struct stat sb;
    if (stat(path, &sb) == -1) {
        return FSTAT_FAIL;
    }

    switch (sb.st_mode & S_IFMT) {
        case S_IFDIR:  return FSTAT_DIR;
        case S_IFREG:  return FSTAT_FILE;
    }

    return FSTAT_MISC;
}

static vm_obj fs_file_exists(vm_obj const & path, vm_obj const &) {
    bool ret = fs_stat(to_string(path).c_str()) == FSTAT_FILE;
    return mk_io_result(mk_vm_bool(ret));
}

static vm_obj fs_dir_exists(vm_obj const & path, vm_obj const &) {
    bool ret = fs_stat(to_string(path).c_str()) == FSTAT_DIR;
    return mk_io_result(mk_vm_bool(ret));
}

static vm_obj fs_remove(vm_obj const & path, vm_obj const &) {
    if (std::remove(to_string(path).c_str()) != 0) {
        return mk_io_failure(sstream() << "remove failed: " << strerror(errno));
    }
    return mk_io_result(mk_vm_unit());
}

static vm_obj fs_rename(vm_obj const & p1, vm_obj const & p2, vm_obj const &) {
    if (std::rename(to_string(p1).c_str(), to_string(p2).c_str()) != 0) {
        return mk_io_failure(sstream() << "rename failed: " << strerror(errno));
    }
    return mk_io_result(mk_vm_unit());
}

int mkdir_single(const char *path) {
#if defined(__linux__) || defined(__APPLE__)
    return mkdir(path, 0777);
#else
    return !CreateDirectoryA(path, NULL);
#endif
}

// Source: https://gist.github.com/JonathonReinhart/8c0d90191c38af2dcadb102c4e202950
int mkdir_recursive(const char *path) {
    // Adapted from http://stackoverflow.com/a/2336245/119527
    const size_t len = strlen(path);
    char _path[PATH_MAX];
    char *p;

    errno = 0;

    /* Copy string so its mutable */
    if (len > sizeof(_path)-1) {
        errno = ENAMETOOLONG;
        return -1;
    }
    snprintf(_path, PATH_MAX, "%s", path);

    /* Iterate the string */
    for (p = _path + 1; *p; p++) {
        if (*p == '/' || *p == '\\') {
            /* Temporarily truncate */
            char tmp = *p;
            *p = '\0';

            if (mkdir_single(_path) != 0) {
                if (errno != EEXIST)
                    return -1;
            }

            *p = tmp;
        }
    }

    if (mkdir_single(_path) != 0) {
        if (errno != EEXIST)
            return -1;
    }

    return 0;
}

static vm_obj fs_mkdir(vm_obj const & _path, vm_obj const & rec, vm_obj const &) {
    std::string path = to_string(_path);
    bool res = to_bool(rec) ? mkdir_recursive(path.c_str())
                            : mkdir_single(path.c_str());
    return mk_io_result(mk_vm_bool(!res));
}

static vm_obj fs_rmdir(vm_obj const & path, vm_obj const &) {
    bool res;
#if defined(__linux__) || defined(__APPLE__)
    res = !rmdir(to_string(path).c_str());
#else
    res = RemoveDirectoryA(to_string(path).c_str());
#endif
    return mk_io_result(mk_vm_bool(res));
}

/*
class monad_io_file_system (m : Type → Type → Type) [monad_io m] :=
/- Remark: in Haskell, they also provide  (Maybe TextEncoding) and  NewlineMode -/
(mk_file_handle : string → io.mode → bool → m io.error (handle m))
(is_eof         : (handle m) → m io.error bool)
(flush          : (handle m) → m io.error unit)
(close          : (handle m) → m io.error unit)
(read           : (handle m) → nat → m io.error string)
(write          : (handle m) → string → m io.error unit)
(get_line       : (handle m) → m io.error string)
(stdin          : m io.error (handle m))
(stdout         : m io.error (handle m))
(stderr         : m io.error (handle m))
(exist          : string → m io.error bool)
(remove         : string → m io.error unit)
(rename         : string → m io.error unit)
(mkdir          : string → m io.error unit)
*/
static vm_obj monad_io_file_system_impl () {
    return mk_vm_constructor(0, {
        mk_native_closure(fs_mk_file_handle),
        mk_native_closure(fs_is_eof),
        mk_native_closure(fs_flush),
        mk_native_closure(fs_close),
        mk_native_closure(fs_read),
        mk_native_closure(fs_write),
        mk_native_closure(fs_get_line),
        mk_native_closure(fs_stdin),
        mk_native_closure(fs_stdout),
        mk_native_closure(fs_stderr),
        mk_native_closure(fs_file_exists),
        mk_native_closure(fs_dir_exists),
        mk_native_closure(fs_remove),
        mk_native_closure(fs_rename),
        mk_native_closure(fs_mkdir),
        mk_native_closure(fs_rmdir)});
}

static vm_obj serial_serialize(vm_obj const & h, vm_obj const & e, vm_obj const &) {
    std::ostringstream out;
    serializer s(out);
    s << to_expr(e);

    FILE *f = to_handle(h)->m_file;
    std::string str = out.str();
    fwrite(str.c_str(), str.size(), 1, f);
    if (ferror(f)) {
        clearerr(f);
        return mk_io_failure("serialize failed");
    }

    return mk_io_result(mk_vm_unit());
}

static vm_obj serial_deserialize(vm_obj const & h, vm_obj const &) {
    FILE *f = to_handle(h)->m_file;
    fseek(f, 0, SEEK_END);
    long fsize = ftell(f);
    fseek(f, 0, SEEK_SET);

    char *data = reinterpret_cast<char *>(malloc(fsize));
    ignore(fread(data, fsize, 1, f));
    if (ferror(f)) {
        clearerr(f);
        return mk_io_failure("deserialize failed");
    }

    std::istringstream in(std::string(data, fsize));
    free(data);
    deserializer d(in);

    return mk_io_result(to_obj(read_expr(d)));
}

static vm_obj monad_io_serial_impl () {
    return mk_vm_constructor(0, {
        mk_native_closure(serial_serialize),
        mk_native_closure(serial_deserialize)});
}

stdio to_stdio(vm_obj const & o) {
    switch (cidx(o)) {
    case 0:
        return stdio::PIPED;
    case 1:
        return stdio::INHERIT;
    case 2:
        return stdio::NUL;
    default:
        lean_unreachable()
    }
}

/*
structure spawn_args :=
  (cmd : string)
  /- Add an argument to pass to the process. -/
  (args : list string)
  /- Configuration for the process's stdin handle. -/
  (stdin := stdio.inherit)
  /- Configuration for the process's stdout handle. -/
  (stdout := stdio.inherit)
  /- Configuration for the process's stderr handle. -/
  (stderr := stdio.inherit)
  (cwd : option string)
  (env : list (string × option string))
*/
static vm_obj io_process_spawn(vm_obj const & process_obj, vm_obj const &) {
    std::string cmd = to_string(cfield(process_obj, 0));

    list<std::string> args = to_list<std::string>(cfield(process_obj, 1), [&] (vm_obj const & o) -> std::string {
        return to_string(o);
    });
    auto stdin_stdio = to_stdio(cfield(process_obj, 2));
    auto stdout_stdio = to_stdio(cfield(process_obj, 3));
    auto stderr_stdio = to_stdio(cfield(process_obj, 4));

    optional<std::string> cwd;
    if (!is_none(cfield(process_obj, 5)))
        cwd = to_string(get_some_value(cfield(process_obj, 5)));

    lean::process proc(cmd, stdin_stdio, stdout_stdio, stderr_stdio);

    for (auto arg : args) {
        proc.arg(arg);
    }

    to_list<unit>(cfield(process_obj, 6), [&] (vm_obj const & o) {
        auto k = to_string(cfield(o, 0));
        optional<std::string> v;
        if (!is_none(cfield(o, 1))) v = to_string(get_some_value(cfield(o, 1)));
        proc.set_env(k, v);
        return unit();
    });

    if (cwd) proc.set_cwd(*cwd);

    return mk_io_result(to_obj(proc.spawn()));
}

static vm_obj io_process_wait(vm_obj const & ch, vm_obj const &) {
    return mk_io_result(mk_vm_nat(to_child(ch)->wait()));
}

static vm_obj io_process_sleep(vm_obj const & seconds, vm_obj const &) {
    std::this_thread::sleep_for(std::chrono::seconds(force_to_unsigned(seconds)));
    return mk_io_result(mk_vm_unit());
}

/*
class monad_io_process (m : Type → Type → Type) [monad_io m] :=
(child  : Type)
(stdin  : child → (handle m))
(stdout : child → (handle m))
(stderr : child → (handle m))
(spawn  : io.process.spawn_args → m io.error child)
(wait   : child → m io.error nat)
(sleep  : nat → m io.error unit)
*/
static vm_obj monad_io_process_impl() {
    return mk_vm_constructor(0, {
        mk_native_closure([] (vm_obj const & c) { return to_obj(to_child(c)->get_stdin()); }),
        mk_native_closure([] (vm_obj const & c) { return to_obj(to_child(c)->get_stdout()); }),
        mk_native_closure([] (vm_obj const & c) { return to_obj(to_child(c)->get_stderr()); }),
        mk_native_closure(io_process_spawn),
        mk_native_closure(io_process_wait),
        mk_native_closure(io_process_sleep),
    });
}

static vm_obj io_return(vm_obj const &, vm_obj const & a, vm_obj const &) {
    return mk_io_result(a);
}

static vm_obj io_bind(vm_obj const & /* α */, vm_obj const & /* β */, vm_obj const & a, vm_obj const & b, vm_obj const &) {
    vm_obj r = invoke(a, mk_vm_unit());
    if (cidx(r) == 0) {
        vm_obj v = cfield(r, 0);
        return invoke(b, v, mk_vm_unit());
    } else {
        return r;
    }
}

static vm_obj io_monad(vm_obj const &) {
    vm_state & S = get_vm_state();
    vm_obj const & mk_monad = S.get_constant(get_monad_from_pure_bind_name());
    return invoke(mk_monad, mk_vm_simple(0), mk_native_closure(io_return), mk_native_closure(io_bind));
}

static vm_obj io_catch(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const & a, vm_obj const & b, vm_obj const &) {
    vm_obj r = invoke(a, mk_vm_unit());
    if (cidx(r) == 1) {
        vm_obj e = cfield(r, 0);
        return invoke(b, e, mk_vm_unit());
    } else {
        return r;
    }
}

static vm_obj io_fail(vm_obj const &, vm_obj const &, vm_obj const & e, vm_obj const &) {
    return mk_io_failure(e);
}

/* (iterate  : Π e α, α → (α → m e (option α)) → m e α) */
static vm_obj io_iterate(vm_obj const &, vm_obj const &, vm_obj const & a, vm_obj const & fn, vm_obj const &) {
    vm_obj r = a;
    while (true) {
        vm_obj p = invoke(fn, r, mk_vm_unit());
        if (cidx(p) == 1) {
            return p;
        } else {
            vm_obj v = cfield(p, 0);
            if (is_none(v)) {
                return mk_io_result(r);
            } else {
                r = get_some_value(v);
            }
        }
    }
}

static vm_obj io_get_env(vm_obj const & k, vm_obj const &) {
    if (auto v = getenv(to_string(k).c_str())) {
        return mk_io_result(mk_vm_some(to_obj(std::string(v))));
    } else {
        return mk_io_result(mk_vm_none());
    }
}

static vm_obj io_get_cwd(vm_obj const &) {
    char buffer[PATH_MAX];
    auto cwd = getcwd(buffer, sizeof(buffer));
    if (cwd) {
        return mk_io_result(to_obj(std::string(cwd)));
    } else {
        return mk_io_failure("get_cwd failed");
    }
}

static vm_obj io_set_cwd(vm_obj const & cwd, vm_obj const &) {
    if (chdir(to_string(cwd).c_str()) == 0) {
        return mk_io_result(mk_vm_unit());
    } else {
        return mk_io_failure("set_cwd failed");
    }
}

/*
class monad_io_environment (m : Type → Type → Type) :=
(get_env : string → m io.error (option string))
-- we don't provide set_env as it is (thread-)unsafe (at least with glibc)
(get_cwd : m io.error string)
(set_cwd : string → m io.error unit)
*/
vm_obj monad_io_environment_impl() {
    return mk_vm_constructor(0, {
            mk_native_closure(io_get_env),
            mk_native_closure(io_get_cwd),
            mk_native_closure(io_set_cwd),
    });
}

/*
class monad_io (m : Type → Type → Type) :=
[monad    : Π e, monad (m e)]
-- TODO(Leo): use monad_except after it is merged
(catch    : Π e₁ e₂ α, m e₁ α → (e₁ → m e₂ α) → m e₂ α)
(fail     : Π e α, e → m e α)
(iterate  : Π e α, α → (α → m e (option α)) → m e α)
-- Primitive Types
(handle   : Type)
*/
vm_obj monad_io_impl() {
    return mk_vm_constructor(0, {
        mk_native_closure(io_monad),
        mk_native_closure(io_catch),
        mk_native_closure(io_fail),
        mk_native_closure(io_iterate)});
    /* field handle is erased */
}

static std::vector<std::string> * g_cmdline_args = nullptr;

void set_io_cmdline_args(std::vector<std::string> const & args) {
    *g_cmdline_args = args;
}

/*
class monad_io_terminal (m : Type → Type → Type) :=
(put_str      : string → m io.error unit)
(get_line     : m io.error string)
(cmdline_args : list string)
*/
vm_obj monad_io_terminal_impl() {
    return mk_vm_constructor(0, {
            mk_native_closure(io_put_str),
            mk_native_closure(io_get_line),
            cmdline_args_to_obj(*g_cmdline_args)});
}

optional<vm_obj> is_io_result(vm_obj const & o) {
    if (cidx(o) == 0)
        return some(cfield(o, 0));
    else
        return optional<vm_obj>();
}

optional<vm_obj> is_io_error(vm_obj const & o) {
    if (cidx(o) == 1)
        return some(cfield(o, 0));
    else
        return optional<vm_obj>();
}

/*
inductive io.error
| other     : string → io.error
| sys       : nat → io.error
*/
std::string io_error_to_string(vm_obj const & o) {
    if (cidx(o) == 0) {
        return to_string(cfield(o, 0));
    } else if (cidx(o) == 1) {
        return (sstream() << "system error #" << to_unsigned(cfield(o, 0))).str();
    }
    lean_vm_check(false);
    lean_unreachable();
}

MK_THREAD_LOCAL_GET_DEF(vm_obj, get_rand_gen);

vm_obj io_set_rand_gen(vm_obj const & g, vm_obj const &) {
    get_rand_gen() = g;
    return mk_io_result(mk_vm_unit());
}

vm_obj io_rand(vm_obj const & lo, vm_obj const & hi, vm_obj const &) {
    vm_obj & gen = get_rand_gen();
    if (is_simple(gen)) {
        if (optional<unsigned> lo1 = try_to_unsigned(lo)) {
            if (optional<unsigned> hi1 = try_to_unsigned(hi)) {
                unsigned r = 0;
                if (*lo1 < *hi1) {
                    r = *lo1 + (std::rand() % (*hi1 - *lo1)); // NOLINT
                }
                return mk_io_result(mk_vm_nat(r));
            }
        }
        mpz const & lo1 = vm_nat_to_mpz1(lo);
        mpz const & hi1 = vm_nat_to_mpz2(hi);
        mpz r(0);
        if (lo1 < hi1) {
            r = lo1 + (mpz(std::rand()) % (hi1 - lo1)); // NOLINT
        }
        return mk_io_result(mk_vm_nat(r));
    } else {
        vm_obj io_rand_nat = get_vm_state().get_constant(get_io_rand_nat_name());
        vm_obj r           = invoke(io_rand_nat, gen, lo, hi);
        gen = cfield(r, 1);
        return mk_io_result(cfield(r, 0));
    }
}

vm_obj monad_io_random_impl() {
    return mk_vm_constructor(0, {
            mk_native_closure(io_set_rand_gen),
            mk_native_closure(io_rand) });
}

void initialize_vm_io() {
#if !(defined(__linux__) || defined(__APPLE__))
    WSADATA wsaData;
    int err = WSAStartup(MAKEWORD(2, 2), &wsaData);
    if (err != 0) {
        fprintf(stderr, "WSAStartup failed with error: %d\n", err);
        exit(1);
    }
#endif

    DECLARE_VM_BUILTIN(name("io_core"), io_core);
    DECLARE_VM_BUILTIN(name("monad_io_impl"), monad_io_impl);
    DECLARE_VM_BUILTIN(name("monad_io_terminal_impl"), monad_io_terminal_impl);
    DECLARE_VM_BUILTIN(name("monad_io_net_system_impl"), monad_io_net_system_impl);
    DECLARE_VM_BUILTIN(name("monad_io_file_system_impl"), monad_io_file_system_impl);
    DECLARE_VM_BUILTIN(name("monad_io_serial_impl"), monad_io_serial_impl);
    DECLARE_VM_BUILTIN(name("monad_io_environment_impl"), monad_io_environment_impl);
    DECLARE_VM_BUILTIN(name("monad_io_process_impl"), monad_io_process_impl);
    DECLARE_VM_BUILTIN(name("monad_io_random_impl"), monad_io_random_impl);
    g_cmdline_args = new std::vector<std::string>();
}

void finalize_vm_io() {
    delete g_cmdline_args;
}
}
