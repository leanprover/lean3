%module environment
%{
#include "kernel/environment.h"
using namespace lean;
%}
//environment
// =======================================
// Class definition and methods
// =======================================
class environment_cell {
public:
    environment_cell();
    environment_cell(std::shared_ptr<environment_cell> const & parent);
    ~environment_cell();

    bool has_children() const;
    bool has_parent() const;
    environment parent() const;
    environment mk_child() const;

    level add_uvar_cnstr(name const & n, level const & l);
    level add_uvar_cnstr(name const & n);

    bool is_ge(level const & l1, level const & l2) const;

    optional<int> get_universe_distance(name const & u1, name const & u2) const;
    level get_uvar(name const & n) const;

    void add_builtin(expr const & v);
    void add_builtin_set(expr const & r);

    void add_definition(name const & n, expr const & t, expr const & v, bool opaque = false);
    void add_definition(name const & n, expr const & v, bool opaque = false);
    void add_opaque_definition(name const & n, expr const & t, expr const & v);
    void add_theorem(name const & n, expr const & t, expr const & v);

    void set_opaque(name const & n, bool opaque);

    void add_axiom(name const & n, expr const & t);
    void add_var(name const & n, expr const & t);

    object get_object(name const & n) const;

    optional<object> find_object(name const & n) const;

    bool has_object(name const & n) const;

    expr type_check(expr const & e, context const & ctx = context()) const;

    expr infer_type(expr const & e, context const & ctx = context()) const;

    expr normalize(expr const & e, context const & ctx = context(), bool unfold_opaque = false) const;

    bool is_proposition(expr const & e, context const & ctx = context()) const;

    unsigned get_num_objects(bool local) const;



    typedef std::unique_ptr<environment_extension> (*mk_extension)();
    static unsigned register_extension(mk_extension mk);

    template<typename Ext>
    Ext const & get_extension(unsigned extid) const {
        environment_extension const & ext = get_extension_core(extid);
        lean_assert(dynamic_cast<Ext const *>(&ext) != nullptr);
        return static_cast<Ext const &>(ext);
    }

    template<typename Ext>
    Ext & get_extension(unsigned extid) {
        environment_extension & ext = get_extension_core(extid);
        lean_assert(dynamic_cast<Ext*>(&ext) != nullptr);
        return static_cast<Ext&>(ext);
    }

    void export_objects(std::string const & fname);
    bool import_state(std::string const & fname, io_state const & ios);
    void load(std::string const & fname, io_state const & ios);
    bool imported(std::string const & n) const;

    void set_trusted_imported(bool flag);

    void auxiliary_section(std::function<void()> fn);
};

/**
   \brief Frontend can store data in environment extensions.
   Each extension is associated with a unique token/id.
   This token allows the frontend to retrieve/store an extension object
   in the environment
*/
class environment_extension {
    friend class environment_cell;
    environment_cell * m_env;
    unsigned           m_extid; // extension id
    environment_extension const * get_parent_core() const;
public:
    environment_extension();
    virtual ~environment_extension();
    /**
       \brief Return a constant reference for a parent extension,
       and a nullptr if there is no parent/ancestor, or if the
       parent/ancestor has an extension.
    */
    template<typename Ext> Ext const * get_parent() const {
        environment_extension const * ext = get_parent_core();
        lean_assert(!ext || dynamic_cast<Ext const *>(ext) != nullptr);
        return static_cast<Ext const *>(ext);
    }
};

/**
   \brief Reference to environment
*/
class environment {
    friend class ro_environment;
    friend class environment_cell;
    friend class read_write_shared_environment;
    std::shared_ptr<environment_cell> m_ptr;
    environment(std::shared_ptr<environment_cell> const & parent, bool);
    environment(std::shared_ptr<environment_cell> const & ptr);
public:
    environment();
    environment_cell * operator->() const { return m_ptr.get(); }
    environment_cell & operator*() const { return *(m_ptr.get()); }
};

/**
   \brief Read-only reference to environment.
*/
class ro_environment {
public:
    typedef std::weak_ptr<environment_cell const> weak_ref;
    ro_environment(environment const & env);
    ro_environment(weak_ref const & env);
    explicit operator weak_ref() const;
    weak_ref to_weak_ref() const;
};


bool is_begin_import(object const & obj);
bool is_begin_builtin_import(object const & obj);
bool is_end_import(object const & obj);
optional<std::string> get_imported_module(object const & obj);

typedef std::function<expr()> mk_builtin_fn;
/**
   \brief Register a builtin or builtin-set that is available to be added to
   a Lean environment.
*/
void register_builtin(name const & n, mk_builtin_fn mk, bool is_builtin_set);
struct register_builtin_fn {
    register_builtin_fn(name const & n, mk_builtin_fn mk, bool is_builtin_set = false);
};

optional<std::pair<expr, bool>> get_builtin(name const & n);

bool is_set_opaque(object const & obj);
name const & get_set_opaque_id(object const & obj);
bool get_set_opaque_flag(object const & obj);
