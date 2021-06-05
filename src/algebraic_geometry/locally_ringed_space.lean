import topology.category.Top_sheaves rings.basic rings.limits

open hott.algebra

universes u v w
hott_theory

namespace hott

namespace algebraic_geometry

@[hott]
structure LocallyRingedSpace extends SheafedSpace CommRing :=
(local_ring : ∀ x, local_ring (presheaf.stalk x))

end algebraic_geometry

end hott
