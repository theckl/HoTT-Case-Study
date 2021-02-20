import topology.basic category_theory

universes u v
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

/- The set of open sets in a topological space. -/
@[hott]
def open_sets := {U ∈ (𝒫 ↥X) | prop_lift (X.top_str.is_open U)}

/- As a subset of the power set the set of open sets automatically receives 
   a precategory instance. Therefore, we can define a presheaf over a 
   topological space with values in a category `C` as follows: -/
@[hott]
def presheaf (C : Type u) [category.{v} C] := (↥(open_sets X))ᵒᵖ ⥤ C

end topology

end hott
