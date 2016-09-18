/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Bundled structures
-/
import algebra.group homotopy.interval
open algebra

namespace algebra
structure Semigroup :=
(carrier : Type) (struct : semigroup carrier)

attribute Semigroup.carrier [coercion]
attribute Semigroup.struct [instance]

structure CommSemigroup :=
(carrier : Type) (struct : comm_semigroup carrier)

attribute CommSemigroup.carrier [coercion]
attribute CommSemigroup.struct [instance]

structure Monoid :=
(carrier : Type) (struct : monoid carrier)

attribute Monoid.carrier [coercion]
attribute Monoid.struct [instance]

structure CommMonoid :=
(carrier : Type) (struct : comm_monoid carrier)

attribute CommMonoid.carrier [coercion]
attribute CommMonoid.struct [instance]

abbreviation signature := interval
structure Group (i : signature) :=
(carrier : Type) (struct : group carrier)

definition MulGroup : Type := Group interval.zero
definition AddGroup : Type := Group interval.one
attribute Group.carrier [coercion]

definition MulGroup.mk [constructor] [reducible] (G : Type) (H : group G) : MulGroup :=
Group.mk _ G _
definition AddGroup.mk [constructor] [reducible] (G : Type) (H : add_group G) : AddGroup :=
Group.mk _ G add_group.to_group

definition MulGroup.struct [reducible] (G : MulGroup) : group G := Group.struct G
definition AddGroup.struct [reducible] (G : AddGroup) : add_group G :=
@group.to_add_group _ (Group.struct G)

attribute MulGroup.struct AddGroup.struct [instance] [priority 2000]
attribute Group.struct [instance] [priority 800]

structure CommGroup (i : signature) :=
(carrier : Type) (struct : comm_group carrier)

definition MulCommGroup : Type := CommGroup interval.zero
definition AddCommGroup : Type := CommGroup interval.one
attribute CommGroup.carrier [coercion]

definition MulCommGroup.mk [constructor] [reducible] (G : Type) (H : comm_group G) : MulCommGroup :=
CommGroup.mk _ G _
definition AddCommGroup.mk [constructor] [reducible] (G : Type) (H : add_comm_group G) :
  AddCommGroup :=
CommGroup.mk _ G add_comm_group.to_comm_group

definition MulCommGroup.struct [reducible] (G : MulCommGroup) : comm_group G := CommGroup.struct G
definition AddCommGroup.struct [reducible] (G : AddCommGroup) : add_comm_group G :=
@comm_group.to_add_comm_group _ (CommGroup.struct G)

attribute MulCommGroup.struct AddCommGroup.struct [instance] [priority 2000]
attribute CommGroup.struct [instance] [priority 800]

-- structure AddSemigroup :=
-- (carrier : Type) (struct : add_semigroup carrier)

-- attribute AddSemigroup.carrier [coercion]
-- attribute AddSemigroup.struct [instance]

-- structure AddCommSemigroup :=
-- (carrier : Type) (struct : add_comm_semigroup carrier)

-- attribute AddCommSemigroup.carrier [coercion]
-- attribute AddCommSemigroup.struct [instance]

-- structure AddMonoid :=
-- (carrier : Type) (struct : add_monoid carrier)

-- attribute AddMonoid.carrier [coercion]
-- attribute AddMonoid.struct [instance]

-- structure AddCommMonoid :=
-- (carrier : Type) (struct : add_comm_monoid carrier)

-- attribute AddCommMonoid.carrier [coercion]
-- attribute AddCommMonoid.struct [instance]

-- structure AddGroup :=
-- (carrier : Type) (struct : add_group carrier)

-- attribute AddGroup.carrier [coercion]
-- attribute AddGroup.struct [instance]

-- structure AddCommGroup :=
-- (carrier : Type) (struct : add_comm_group carrier)

-- attribute AddCommGroup.carrier [coercion]
-- attribute AddCommGroup.struct [instance]
end algebra
