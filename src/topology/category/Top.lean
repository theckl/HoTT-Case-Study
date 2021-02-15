import topology.basic category_theory

universe u
hott_theory

namespace hott
open hott.set hott.subset category_theory

/- The category of topological spaces and continuous maps. -/
@[hott]
structure Top :=
(carrier : Set)
(top_str : topological_space carrier)

@[hott]
instance Top_to_Set : has_coe_to_sort Top.{u} :=
  has_coe_to_sort.mk Set.{u} (λ T : Top, T.carrier)

@[hott]
instance topological_space_unbundled (X : Top) : 
  topological_space ↥X := X.top_str

namespace topology

variables (X : Top.{u})

/- The precategory of open sets in a topological space. 
   Morphisms are inclusions, and we derive the functorial properties of these morphisms 
   from the weak (or partial) order on subsets induced by inclusions. -/
@[hott]
def open_sets := {U ∈ (𝒫 ↥X) | prop_lift (X.top_str.is_open U)}

@[hott, instance]
def open_set_has_hom : has_hom (↥open_sets X) := sorry

end topology

end hott
