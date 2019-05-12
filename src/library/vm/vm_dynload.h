#include <string>
#include <memory>
#include "library/vm/vm.h"

#define FOREIGN_OBJ void *

namespace lean {

    using std::string;

    struct vm_foreign_obj_cell {
        MK_LEAN_RC();
        FOREIGN_OBJ m_handle;
        std::string m_filename;
        vm_foreign_obj_cell(FOREIGN_OBJ handle, string const & filename)
        : m_rc(0), m_handle(handle),
            m_filename(filename) {};
        ~vm_foreign_obj_cell();
        vm_decl get_cfun(name const & n, unsigned idx, string const & fun_name,
                         buffer<expr> const & _args, expr const & _t);
        void dealloc();
    private:
        vm_foreign_obj_cell(vm_foreign_obj_cell const &);

        /* virtual void dealloc() override { */
        /*     this->~vm_foreign_obj(); */
        /*     get_vm_allocator().deallocate(sizeof(vm_foreign_obj), this); */
        /* } */
        /* virtual vm_external * clone(vm_clone_fn const &) override { */
        /*     return new vm_foreign_obj(m_handle, m_filename); */
        /* } */
        /* virtual vm_external * ts_clone(vm_clone_fn const &) override { */
        /*     return new (get_vm_allocator().allocate(sizeof(vm_foreign_obj))) vm_foreign_obj(m_handle, m_filename); */
        /* } */
    };

    class vm_foreign_obj {
    private:
        vm_foreign_obj_cell * m_ptr;
    public:
        vm_foreign_obj():m_ptr(nullptr) {}
        vm_foreign_obj(string const & fname);
        vm_foreign_obj(vm_foreign_obj const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
        vm_foreign_obj(vm_foreign_obj && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
        vm_decl get_cfun(name const & n, unsigned idx, string const & fun_name,
                         buffer<expr> const & _args, expr const & _t) {
            lean_assert(m_ptr); return m_ptr->get_cfun(n, idx, fun_name, _args, _t); }
        vm_foreign_obj & operator=(vm_foreign_obj const & s) { LEAN_COPY_REF(s); }
        vm_foreign_obj & operator=(vm_foreign_obj && s) { LEAN_MOVE_REF(s); }

        ~vm_foreign_obj() { if (m_ptr) { m_ptr->dec_ref(); } }
    };


    /* std::shared_ptr<vm_foreign_obj_cell> load_foreign_obj(string const & fname); */

    void initialize_vm_ffi();

    void finalize_vm_ffi();

    void initialize_vm_ffi();

    void finalize_vm_ffi();

}
