/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Bundled structures
-/
import algebra.group homotopy.interval
open algebra pointed is_trunc

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

structure Group :=
(carrier : Type) (struct : group carrier)

attribute Group.carrier [coercion]
attribute Group.struct [instance]

section
  local attribute Group.struct [instance]
  definition pSet_of_Group [constructor] [reducible] [coercion] (G : Group) : Set* :=
  ptrunctype.mk G !semigroup.is_set_carrier 1
end

attribute algebra._trans_of_pSet_of_Group [unfold 1]
attribute algebra._trans_of_pSet_of_Group_1 algebra._trans_of_pSet_of_Group_2 [constructor]

definition pType_of_Group [reducible] [constructor] : Group → Type* :=
algebra._trans_of_pSet_of_Group_1
definition Set_of_Group [reducible] [constructor] : Group → Set :=
algebra._trans_of_pSet_of_Group_2

definition AddGroup : Type := Group

definition AddGroup.mk [constructor] [reducible] (G : Type) (H : add_group G) : AddGroup :=
Group.mk G H

definition AddGroup.struct [reducible] (G : AddGroup) : add_group G :=
Group.struct G

attribute AddGroup.struct Group.struct [instance] [priority 2000]

structure AbGroup :=
(carrier : Type) (struct : ab_group carrier)

attribute AbGroup.carrier [coercion]

definition AddAbGroup : Type := AbGroup

definition AddAbGroup.mk [constructor] [reducible] (G : Type) (H : add_ab_group G) :
  AddAbGroup :=
AbGroup.mk G H

definition AddAbGroup.struct [reducible] (G : AddAbGroup) : add_ab_group G :=
AbGroup.struct G

attribute AddAbGroup.struct AbGroup.struct [instance] [priority 2000]

definition Group_of_AbGroup [coercion] [constructor] (G : AbGroup) : Group :=
Group.mk G _

attribute algebra._trans_of_Group_of_AbGroup_1
          algebra._trans_of_Group_of_AbGroup
          algebra._trans_of_Group_of_AbGroup_3 [constructor]
attribute algebra._trans_of_Group_of_AbGroup_2 [unfold 1]


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

-- structure AddAbGroup :=
-- (carrier : Type) (struct : add_ab_group carrier)

-- attribute AddAbGroup.carrier [coercion]
-- attribute AddAbGroup.struct [instance]
end algebra
