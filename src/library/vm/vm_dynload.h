#include <string>
#include <memory>

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
      vm_cfunction get_cfun(string const & fun_name);
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

}
