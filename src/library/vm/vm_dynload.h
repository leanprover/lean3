#include <string>
#include <memory>
#include "library/vm/vm.h"

#define FOREIGN_OBJ void *

namespace lean {

    using std::string;

    class vm_foreign_obj {
    private:
      FOREIGN_OBJ m_handle;
      std::string m_filename;
    public:
      vm_foreign_obj(FOREIGN_OBJ handle, string const & filename)
          : m_handle(handle),
            m_filename(filename) {};
      ~vm_foreign_obj();
      vm_decl get_cfun(name const & n, unsigned idx, string const & fun_name,
                       buffer<expr> const & _args, expr const & _t);
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

    std::shared_ptr<vm_foreign_obj> load_foreign_obj(string const & fname);

    void initialize_vm_ffi();

    void finalize_vm_ffi();

}
