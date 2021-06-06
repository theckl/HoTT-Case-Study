import topology.category.Top_sheaves rings.basic rings.limits rings.colimits

open hott.algebra hott.category_theory.limits hott.topology hott.category_theory.colimits

universes u v w
hott_theory

namespace hott

namespace algebraic_geometry

#print fields PresheafedSpace

@[hott]
structure LocallyRingedSpace extends SheafedSpace CommRing :=
(local_ring : ∀ x, local_ring (@stalk to_PresheafedSpace.carrier 
                               CommRing _ (ring_has_colimits) to_PresheafedSpace.presheaf x))

end algebraic_geometry

end hott
