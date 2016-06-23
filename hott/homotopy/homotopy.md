homotopy
========

Development of Homotopy Theory, including basic hits (higher inductive
types; see also [hit](../hit/hit.md)). The following files are in this
folder (sorted such that files only import previous files).

* [connectedness](connectedness.hlean) (n-Connectedness of types and functions)
* [cylinder](cylinder.hlean) (Mapping cylinders, defined using quotients)
* [susp](susp.hlean) (Suspensions, defined using pushouts)
* [sphere](sphere.hlean) (Higher spheres, defined recursively using suspensions)
* [circle](circle.hlean) (defined as sphere 1)
* [interval](interval.hlean) (defined as the suspension of unit)
* [cellcomplex](cellcomplex.hlean) (general cell complexes)
* [cofiber](cofiber.hlean)
* [wedge](wedge.hlean)
* [smash](smash.hlean)
* [join](join.hlean)
* [freudenthal](freudenthal.hlean) (The Freudenthal Suspension Theorem)
* [hopf](hopf.hlean) (the Hopf construction and delooping of coherent connected H-spaces)
* [complex_hopf](complex_hopf.hlean) (the complex Hopf fibration)
* [imaginaroid](imaginaroid.hlean) (imaginaroids as a variant of the Cayley-Dickson construction)
* [quaternionic_hopf](quaternionic_hopf.hlean) (the quaternionic Hopf fibration)
* [chain_complex](chain_complex.hlean)
* [LES_of_homotopy_groups](LES_of_homotopy_groups.hlean)
* [vankampen](vankampen.hlean) (the Seifert-van Kampen theorem)
* [homotopy_group](homotopy_group.hlean) (theorems about homotopy groups. The definition and basic facts about homotopy groups is in [algebra/homotopy_group](../algebra/homotopy_group.hlean))
* [sphere2](sphere2.hlean) (calculation of the homotopy group of spheres)


The following files depend on
[hit.two_quotient](../hit/two_quotient.hlean) which on turn depends on
[circle](circle.hlean).

* [red_susp](red_susp.hlean) (Reduced suspensions)
* [torus](torus.hlean) (defined as a two-quotient)
* [EM](EM.hlean): Eilenberg MacLane spaces
