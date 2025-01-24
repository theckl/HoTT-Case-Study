import topology.category.Top_sheaves rings.basic rings.limits rings.colimits

open hott.algebra hott.category_theory.limits hott.topology hott.category_theory.colimits

universes v v' u u' w
hott_theory

namespace hott

namespace algebraic_geometry

@[hott]
structure LocallyRingedSpace :=
(carrier : Top)
(presheaf : topology.presheaf carrier CommRing)
(sheaf_condition : @topology.sheaf_condition carrier _ _ CommRing_has_products 
                     (presheaf ⋙ ring_ulift_functor)) 
(local_ring : ∀ x, local_ring (@stalk carrier CommRing _ 
                     ring_has_colimits (presheaf ⋙ ring_ulift_functor) x))

end algebraic_geometry

end hott
