import topology.basic category_theory categorial_limits

universes u v w
hott_theory

namespace hott
open hott.set hott.subset hott.category_theory category_theory.limits

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
def open_sets : Subset (𝒫 ↥X) := 
  {U ∈ (𝒫 ↥X) | prop_lift (X.top_str.is_open U)}

/- As a subset of the power set the set of open sets automatically receives 
   a precategory instance. Therefore, we can define a presheaf over a 
   topological space with values in a category `C` as follows: -/
@[hott]
def presheaf (C : Type u) [category.{v} C] := (↥(open_sets X))ᵒᵖ ⥤ C

/- The product of the sections of a presheaf over a family of open sets. -/
@[hott]
def pi_opens {C : Type u} [category.{v} C] [hp : has_products C]
  {I : Set} (U : I -> (open_sets X).carrier) (F : presheaf X C) : C :=
have hls : has_limits_of_shape (discrete I) C, from hp I,    
∏ (λ i : I, F.obj (opposite.op (U i)))

/- The product of the sections of a presheaf over the pairwise intersections 
   of a family of open sets.-/
@[hott]
def pi_inters {C : Type u} [category.{v} C] [has_products C]
  {I : Set} (U : I -> (open_sets X).carrier) (F : presheaf X C) : C :=
∏ (λ p : ↥(I × I), F.obj (opposite.op (U p.1 ∩ U p.2)))

end topology

end hott
