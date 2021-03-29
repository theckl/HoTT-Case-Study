import topology.basic category_theory categorial_limits

universes u v w
hott_theory

namespace hott
open hott.set hott.subset hott.category_theory category_theory.limits
  category_theory.opposite

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

/- The set of open sets in a topological space and its lattice structure. 
   (TODO: constructing supremum and order) -/
@[hott]
def open_sets : Subset (𝒫 ↥X) := 
  {U ∈ (𝒫 ↥X) | prop_ulift (is_open ↥X U)}

@[hott]
instance Subset_Set_to_Set : has_coe_to_sort (Subset (𝒫 ↥X)) :=
  has_coe_to_sort.mk (Type (u+1)) (λ T, T.carrier)

@[hott]
protected def open_sets.inter (U V : open_sets X) : open_sets X :=
have U_is_open : is_open ↥X U, from ulift.down U.2, 
have V_is_open : is_open ↥X V, from ulift.down V.2,
have inter_is_open : prop_ulift (is_open ↥X (↑U ∩ ↑V)), from 
  ulift.up (is_open_inter ↥X U_is_open V_is_open),
elem_pred.{u+1} (↑U ∩ ↑V) inter_is_open  

@[hott, instance]
def open_sets_inter : has_inter (open_sets X) :=
⟨open_sets.inter X⟩    

@[hott]
def open_sets.iUnion {I : Set} (f : I -> open_sets X) : (open_sets X) :=
have U_i_is_open : ∀ i : I, is_open ↥X (f i), from 
  assume i, ulift.down (f i).2, 
have open_union : is_open ↥X (⋃ᵢ ↑f), from
  is_open_iUnion ↥X U_i_is_open,  
elem_pred.{u+1} (⋃ᵢ ↑f) (ulift.up open_union)    

/- As a subset of the power set the set of open sets automatically receives 
   a precategory instance. Therefore, we can define a presheaf over a 
   topological space with values in a category `C` as follows: -/
@[hott]
def presheaf (C : Type u) [category.{v} C] := (open_sets X)ᵒᵖ ⥤ C

/- The product of the sections of a presheaf over a family of open sets. -/
@[hott]
def pi_opens {C : Type u} [category.{v} C] [has_products C] 
  {I : Set} (U : I -> open_sets X) (F : presheaf X C) : C :=   
∏ (λ i : I, F.obj (op (U i)))

/- The product of the sections of a presheaf over the pairwise intersections 
   of a family of open sets.-/
@[hott]
def pi_inters {C : Type u} [category.{v} C] [has_products C]
  {I : Set} (U : I -> open_sets X) (F : presheaf X C) : C :=  
∏ (λ p : ↥(I × I), F.obj (op (U p.1 ∩ U p.2)))

@[hott]
def left_res {C : Type u} [category.{v} C] [has_products C]
  {I : Set} (U : I -> open_sets X) (F : presheaf X C) : 
  (pi_opens X U F) ⟶ (pi_inters X U F) :=
pi.lift C (λ p : ↥I × I, pi.π _ p.1 ≫ 
                            F.map (hom_op (inter_sset_l (U p.1) (U p.2))))

@[hott]
def right_res {C : Type u} [category.{v} C] [has_products C]
  {I : Set} (U : I -> open_sets X) (F : presheaf X C) : 
  (pi_opens X U F) ⟶ (pi_inters X U F) :=
pi.lift C (λ p : ↥I × I, pi.π _ p.2 ≫ 
                            F.map (hom_op (inter_sset_r (U p.1) (U p.2))))

@[hott]
def res {C : Type u} [category.{v} C] [has_products C]
  {I : Set} (U : I -> open_sets X) (F : presheaf X C) :
  (F.obj (op (open_sets.iUnion X U))) ⟶ (pi_opens X U F) :=  
pi.lift C (λ i : I, F.map (hom_op (sset_iUnion ↑U i))) 

@[hott]
def w_res {C : Type u} [category.{v} C] [has_products C]
  {I : Set.{u}} (U : I -> open_sets X) (F : presheaf X C) :
  (res X U F) ≫ (left_res X U F) = (res X U F) ≫ (right_res X U F) :=    
calc (res X U F) ≫ (left_res X U F) = pi.lift C (λ p : ↥I × I, 
                          ((res X U F) ≫ (left_res X U F)) ≫ pi.π _ p) :
           pi.hom_is_lift C ((res X U F) ≫ (left_res X U F))
     ... = pi.lift C (λ p : ↥I × I, F.map (hom_op (sset_iUnion ↑U p.1)) ≫
                          F.map (hom_op (inter_sset_l (U p.1) (U p.2)))) :
           sorry               
     ... = (res X U F) ≫ (right_res X U F) : sorry                  

@[hott]
def sheaf_condition_equalizer_products.fork {C : Type u} [category.{v} C] 
  [hp : has_products C] {I : Set} (U : I -> (open_sets X).carrier) 
  (F : presheaf X C) : fork (left_res X U F) (right_res X U F) :=
sorry                            

end topology

end hott
