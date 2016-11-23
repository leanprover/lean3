algebra
=======

The following files are [ported](../port.md) from the standard library. If anything needs to be changed, it is probably a good idea to change it in the standard library and then port the file again (see also [script/port.pl](../../script/port.pl)).

* [priority](priority.hlean) : priority for algebraic operations
* [relation](relation.hlean)
* [binary](binary.hlean) : binary operations
* [order](order.hlean)
* [lattice](lattice.hlean)
* [group](group.hlean)
* [ring](ring.hlean)
* [ordered_group](ordered_group.hlean)
* [ordered_ring](ordered_ring.hlean)
* [field](field.hlean)
* [ordered_field](ordered_field.hlean)
* [bundled](bundled.hlean) : bundled versions of the algebraic structures

Files which are not ported from the standard library:

* [group_theory](group_theory.hlean) : Basic theorems about group homomorphisms and isomorphisms
* [trunc_group](trunc_group.hlean) : truncate an infinity-group to a group
* [homotopy_group](homotopy_group.hlean) : homotopy groups of a pointed type
* [e_closure](e_closure.hlean) : the type of words formed by a relation
* [graph](graph.hlean) : definition and operations on paths in a graph.

Subfolders (not ported):

* [category](category/category.md) : Category Theory
