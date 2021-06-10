import topology.category.Top_sheaves rings.basic rings.limits rings.colimits

open hott.algebra hott.category_theory.limits hott.topology hott.category_theory.colimits

universes v u w
hott_theory

namespace hott

namespace algebraic_geometry

set_option pp.universes true

#print ring_has_colimits

@[hott]
structure LocallyRingedSpace extends SheafedSpace.{u u+1 u} CommRing.{u} :=
(local_ring : ∀ x, local_ring (@stalk.{u u+1 u} to_PresheafedSpace.carrier 
                               CommRing _ (ring_has_colimits) to_PresheafedSpace.presheaf x))

end algebraic_geometry

end hott
