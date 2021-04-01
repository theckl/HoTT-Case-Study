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

/- The set of open sets in a topological space and its lattice structure. -/
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

@[hott]
def open_sets_incl_to_hom {U V : open_sets X} (i : @is_subset_of ↥X ↑U ↑V) : 
  U ⟶ V := i 

@[hott]
def opens.inf_le_l (U V : open_sets X) : U ∩ V ⟶ U :=
  inter_sset_l U V 

@[hott]
def opens.inf_le_r (U V : open_sets X) : U ∩ V ⟶ V :=
  inter_sset_r U V 

@[hott]
def opens.le_union {I : Set} (f : I -> open_sets X) :
  Π i : I, f i ⟶ open_sets.iUnion X f :=
assume i, sset_iUnion ↑f i       

@[hott]
def opens.hom_eq {U V : open_sets X} (f g : U ⟶ V) : f = g :=
  power_set_unique_hom f g 

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

@[hott, reducible]
def left_res {C : Type u} [category.{v} C] [has_products C]
  {I : Set} (U : I -> open_sets X) (F : presheaf X C) : 
  (pi_opens X U F) ⟶ (pi_inters X U F) :=
pi.lift C (λ p : ↥(I × I), pi.π _ p.1 ≫ 
                        F.map (hom_op (opens.inf_le_l X (U p.1) (U p.2))))

@[hott, reducible]
def right_res {C : Type u} [category.{v} C] [has_products C]
  {I : Set} (U : I -> open_sets X) (F : presheaf X C) : 
  (pi_opens X U F) ⟶ (pi_inters X U F) :=
pi.lift C (λ p : ↥I × I, pi.π _ p.2 ≫ 
                       F.map (hom_op (opens.inf_le_r X (U p.1) (U p.2))))

@[hott, reducible]
def res {C : Type u} [category.{v} C] [has_products C]
  {I : Set} (U : I -> open_sets X) (F : presheaf X C) :
  (F.obj (op (open_sets.iUnion X U))) ⟶ (pi_opens X U F) :=  
pi.lift C (λ i : I, F.map (hom_op (opens.le_union X U i))) 

@[hott]
def w_res {C : Type u} [category.{v} C] [has_products C]
  {I : Set.{u}} (U : I -> open_sets X) (F : presheaf X C) :
  (res X U F) ≫ (left_res X U F) = (res X U F) ≫ (right_res X U F) :=  
have left_eq : Π p : ↥(I × I), ((res X U F) ≫ (left_res X U F)) ≫ pi.π _ p =
  F.map (hom_op (opens.inf_le_l X (U p.1) (U p.2) ≫ opens.le_union X U p.1)), from
  assume p,
  calc ((res X U F) ≫ (left_res X U F)) ≫ pi.π _ p = 
             (res X U F) ≫ ((left_res X U F) ≫ pi.π _ p) : precategory.assoc _ _ _
       ... = (res X U F) ≫ (pi.π _ p.1 ≫ F.map (hom_op (opens.inf_le_l X (U p.1) (U p.2)))) :
             by rwr pi.lift_π_eq C _ p 
       ... = ((res X U F) ≫ pi.π _ p.1) ≫ F.map (hom_op (opens.inf_le_l X (U p.1) (U p.2))) :           
             (precategory.assoc _ _ _)⁻¹
       ... = F.map (hom_op (opens.le_union X U p.1)) ≫ 
                                      F.map (hom_op (opens.inf_le_l X (U p.1) (U p.2))) :
             by rwr pi.lift_π_eq C _ p.1 
       ... = F.map (hom_op (opens.le_union X U p.1) ≫ 
                                             hom_op (opens.inf_le_l X (U p.1) (U p.2))) : 
             (functor.map_comp F _ _)⁻¹
       ... = F.map (hom_op (opens.inf_le_l X (U p.1) (U p.2) ≫ opens.le_union X U p.1)) : 
             by rwr <- hom_op_funct _ _,
have right_eq : Π p : ↥(I × I), ((res X U F) ≫ (right_res X U F)) ≫ pi.π _ p =
  F.map (hom_op (opens.inf_le_r X (U p.1) (U p.2) ≫ opens.le_union X U p.2)), from
  assume p,
  calc ((res X U F) ≫ (right_res X U F)) ≫ pi.π _ p = 
             (res X U F) ≫ ((right_res X U F) ≫ pi.π _ p) : precategory.assoc _ _ _
       ... = (res X U F) ≫ (pi.π _ p.2 ≫ F.map (hom_op (opens.inf_le_r X (U p.1) (U p.2)))) :
             by rwr pi.lift_π_eq C _ p 
       ... = ((res X U F) ≫ pi.π _ p.2) ≫ F.map (hom_op (opens.inf_le_r X (U p.1) (U p.2))) :           
             (precategory.assoc _ _ _)⁻¹
       ... = F.map (hom_op (opens.le_union X U p.2)) ≫ 
                                      F.map (hom_op (opens.inf_le_r X (U p.1) (U p.2))) :
             by rwr pi.lift_π_eq C _ p.2 
       ... = F.map (hom_op (opens.le_union X U p.2) ≫ 
                                             hom_op (opens.inf_le_r X (U p.1) (U p.2))) : 
             (functor.map_comp F _ _)⁻¹
       ... = F.map (hom_op (opens.inf_le_r X (U p.1) (U p.2) ≫ opens.le_union X U p.2)) : 
             by rwr <- hom_op_funct _ _,
have incl_eq : Π p : ↥I × I, (opens.inf_le_l X (U p.1) (U p.2) ≫ opens.le_union X U p.1) =
                      (opens.inf_le_r X (U p.1) (U p.2) ≫ opens.le_union X U p.2), from
  assume p, opens.hom_eq X _ _,                      
have left_right_eq : Π p : ↥I × I, ((res X U F) ≫ (left_res X U F)) ≫ pi.π _ p =
  ((res X U F) ≫ (right_res X U F)) ≫ pi.π _ p, from assume p,
  calc ((res X U F) ≫ (left_res X U F)) ≫ pi.π _ p = 
          F.map (hom_op (opens.inf_le_l X (U p.1) (U p.2) ≫ opens.le_union X U p.1)) : 
          left_eq p
    ... = F.map (hom_op (opens.inf_le_r X (U p.1) (U p.2) ≫ opens.le_union X U p.2)) : 
          by rwr incl_eq p
    ... = ((res X U F) ≫ (right_res X U F)) ≫ pi.π _ p : (right_eq p)⁻¹,
have fun_lr_eq : (λ p : ↥I × I, ((res X U F) ≫ (left_res X U F)) ≫ pi.π _ p) =
  λ p : ↥I × I, ((res X U F) ≫ (right_res X U F)) ≫ pi.π _ p, from 
  eq_of_homotopy (λ p, left_right_eq p),                           
calc (res X U F) ≫ (left_res X U F) = pi.lift C (λ p : ↥I × I, 
                          ((res X U F) ≫ (left_res X U F)) ≫ pi.π _ p) :
           pi.hom_is_lift C ((res X U F) ≫ (left_res X U F))
     ... = pi.lift C (λ p : ↥I × I, 
                          ((res X U F) ≫ (right_res X U F)) ≫ pi.π _ p) :
           by rwr fun_lr_eq                                  
     ... = (res X U F) ≫ (right_res X U F) : 
           (pi.hom_is_lift C ((res X U F) ≫ (right_res X U F)))⁻¹                  
/- Of course, this proof is way too long. In [mathlib], most of the calculations are simplified,
   but that makes the idea of the proof completely invisible. The challenge is to translate the
   manipulations in the associated commutative diagram to a readable proof. One of the problems
  are the long names. -/

@[hott]
def sheaf_condition_equalizer_products.fork {C : Type u} [category.{v} C] 
  [has_products C] {I : Set} (U : I -> open_sets X) 
  (F : presheaf X C) : fork (left_res X U F) (right_res X U F) :=
fork.of_i _ _ (res X U F) (w_res X U F)

@[hott]
def sheaf_condition {C : Type u} [category.{v} C] [has_products C] (F : presheaf X C) := Π {I : Set} (U : I -> open_sets X), 
  is_limit (sheaf_condition_equalizer_products.fork X U F)

@[hott]
structure sheaf (C : Type u) [category.{v} C] [has_products C] :=
(presheaf : presheaf X C)
(sheaf_condition : sheaf_condition X presheaf)

end topology

@[hott]
structure PresheafedSpace (C : Type u) [category.{v} C] :=
  (carrier : Top)
  (presheaf : topology.presheaf carrier C)

@[hott]
structure SheafedSpace (C : Type u) [category.{v} C] [has_products C] extends 
  PresheafedSpace C := 
  (sheaf_condition : topology.sheaf_condition carrier presheaf)   

end hott
