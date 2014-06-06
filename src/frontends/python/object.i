%module object
%{
#include "kernel/object.h"
using namespace lean;
%}
//obj
// =======================================
// Class definition and methods
// =======================================
class object {
public:
    object(object const & s);
    object(object && s);
    ~object();

    friend void swap(object & a, object & b);

    object_kind kind() const;

    friend object mk_uvar_cnstr(name const & n, level const & l);
    friend object mk_definition(name const & n, expr const & t, expr const & v, unsigned weight);
    friend object mk_theorem(name const & n, expr const & t, expr const & v);
    friend object mk_axiom(name const & n, expr const & t);
    friend object mk_var_decl(name const & n, expr const & t);
    friend object mk_neutral(neutral_object_cell * c);
    friend object mk_builtin(expr const & v);
    friend object mk_builtin_set(expr const & r);

    char const * keyword() const;
    bool has_name() const;
    name get_name() const;
    bool has_type() const;
    bool has_cnstr_level() const;
    level get_cnstr_level() const;
    expr get_type() const;
    bool is_definition() const;
    bool is_opaque() const;
    expr get_value() const;
    unsigned get_weight() const;

    bool is_axiom() const;
    bool is_theorem() const;
    bool is_var_decl() const;
    bool is_builtin() const;
    bool is_builtin_set() const;
    bool in_builtin_set(expr const & e) const;

    void write(serializer & s) const;

    object_cell const * cell() const;
};

// =======================================
// Constructors
object mk_uvar_cnstr(name const & n, level const & l);
object mk_builtin(expr const & v);
object mk_builtin_set(expr const & r);
object mk_definition(name const & n, expr const & t, expr const & v, unsigned weight);
object mk_theorem(name const & n, expr const & t, expr const & v);
object mk_axiom(name const & n, expr const & t);
object mk_var_decl(name const & n, expr const & t);
object mk_neutral(neutral_object_cell * c);


// Unfolding
bool should_unfold(object const & obj, bool unfold_opaque);
