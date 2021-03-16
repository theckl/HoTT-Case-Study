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

/- The set of open sets in a topological space and its lattice structure. -/
@[hott]
def open_sets : Subset (𝒫 ↥X) := 
  {U ∈ (𝒫 ↥X) | prop_lift (X.top_str.is_open U)}

@[hott]
def open_set_is_open (U : (open_sets X).carrier) : X.top_str.is_open U :=
  sorry

@[hott]
protected def open_sets.inter (U V : (open_sets X).carrier) : 
  (open_sets X).carrier :=
have U_is_open : X.top_str.is_open U, from open_set_is_open X U, 
have V_is_open : X.top_str.is_open V, from open_set_is_open X V,
have inter_is_open : X.top_str.is_open (↑U ∩ ↑V), from 
  X.top_str.is_open_inter U V U_is_open V_is_open, 
sorry

@[hott, instance]
def open_sets_inter : has_inter (open_sets X).carrier :=
⟨open_sets.inter X⟩    

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
def pi_inters {C : Type u} [category.{v} C] [hp : has_products C]
  {I : Set} (U : I -> (open_sets X).carrier) (F : presheaf X C) : C :=
have hls : has_limits_of_shape (discrete (I × I)) C, from hp (I × I),  
∏ (λ p : ↥(I × I), F.obj (opposite.op (U p.1 ∩ U p.2)))

end topology

end hott
