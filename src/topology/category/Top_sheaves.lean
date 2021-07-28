import topology.basic categories.cat_limits categories.cat_colimits

universes v v' u u' w w'
hott_theory

namespace hott
open hott.set hott.subset hott.categories category_theory.limits category_theory.colimits
  categories.opposite hott.sigma hott.is_trunc

set_option pp.universes false  

/- The category of topological spaces and continuous maps. -/
@[hott]
structure Top :=
(carrier : Set)
(top_str : topological_space carrier)

@[hott]
instance Top_to_Set : has_coe_to_sort Top :=
  has_coe_to_sort.mk Set (λ T : Top, T.carrier)

@[hott]
instance topological_space_unbundled (X : Top) : 
  topological_space ↥X := X.top_str

variables (X : Top)

namespace topology

/- The set of open sets in a topological space and its lattice structure. -/
@[hott]
def open_sets : Subset (𝒫 ↥X) := 
  {U ∈ (𝒫 ↥X) | is_open ↥X U}

@[hott]
instance Subset_Set_to_Set : has_coe_to_sort (Subset (𝒫 ↥X)) :=
  has_coe_to_sort.mk (Type _) (λ T, T.carrier)

@[hott]
instance : has_coe ↥(open_sets X) (Subset ↥X) :=
  ⟨λ Y : ↥(open_sets X), (open_sets X).map Y⟩

@[hott]
protected def open_sets.inter (U V : open_sets X) : open_sets X :=
have U_is_open : is_open ↥X U, from U.2, 
have V_is_open : is_open ↥X V, from V.2,
have inter_is_open : is_open ↥X (((open_sets X).map U) ∩ ((open_sets X).map V)), from 
  is_open_inter ↥X U_is_open V_is_open,
elem_pred (((open_sets X).map U) ∩ ((open_sets X).map V)) inter_is_open  

@[hott, instance]
def open_sets_inter : has_inter (open_sets X) :=
⟨open_sets.inter X⟩    

@[hott]
def open_sets.iUnion {I : Set} (f : I -> open_sets X) : ↥(open_sets X) :=
have U_i_is_open : ∀ i : I, is_open ↥X (f i), from assume i, (f i).2, 
have open_union : is_open ↥X (⋃ᵢ (λ i, (f i).1)), from is_open_iUnion ↥X U_i_is_open,  
elem_pred (⋃ᵢ (λ i, (f i).1)) open_union    

@[hott]
def open_sets_incl_to_hom {U V : open_sets X} (i : ((open_sets X).map U) ⊆ ((open_sets X).map V)) : 
  U ⟶ V := i 

@[hott]
def open_sets_hom_to_emb {U V : open_sets X} (i : U ⟶ V) : U.1.carrier -> V.1.carrier :=
  assume x, elem_obj ↑x (i ↑x (obj_elem x))

@[hott]
def opens.inf_le_l (U V : open_sets X) : open_sets.inter X U V ⟶ U :=
  inter_sset_l U V 

@[hott]
def opens.inf_le_r (U V : open_sets X) : open_sets.inter X U V ⟶ V :=
  inter_sset_r U V 

@[hott]
def opens.le_union {I : Set} (f : I -> open_sets X) :
  Π i : I, f i ⟶ open_sets.iUnion X f :=   
begin 
  intro i, apply open_sets_incl_to_hom, 
  change ↥(↑(f i) ⊆ ↑(open_sets.iUnion X f)), 
  exact sset_iUnion (λ i, ↑(f i)) i
end       

@[hott]
def opens.hom_eq {U V : open_sets X} (f g : U ⟶ V) : f = g :=
  power_set_unique_hom f g 

@[hott, reducible] 
def nbhds (x : X.carrier) : Subset (𝒫 ↥X) := 
  {U ∈ (𝒫 ↥X) | is_open ↥X U and x ∈ U} 

@[hott]
def nbhds_opens_inc (x : X.carrier) : nbhds X x ⊆ open_sets X :=
begin 
  intros U el,   
  have el' : ↥(U∈pred_to_sset (λ (a : ↥𝒫↥X), is_open ↥X a and x∈a)), 
    from el,
  have H : ↥(is_open ↥X U and x∈U), from (elem_to_pred U) el', 
  exact (pred_to_elem U) H.1 
end

@[hott, instance]
def nbhds_precat (x : X.carrier) : precategory (nbhds X x) :=
  subset_precat_precat (nbhds X x)

@[hott]
def nbhds_opens_inc_functor (x : X.carrier) : (nbhds X x)ᵒᵖ ⥤ (open_sets X)ᵒᵖ :=
  opposite_functor (functor_subsets_precat (nbhds_opens_inc X x))

/- As a subset of the power set the set of open sets (and sets of neighborhoods) automatically
   receive a precategory instance. Therefore, we can define a presheaf over a 
   topological space with values in a category `C` and its stalks as follows: -/
@[hott]
def presheaf (C : Type u') [category.{v'} C] := (open_sets X)ᵒᵖ ⥤ C

@[hott]
def stalk (C : Type u') [category.{v'} C] [H : has_colimits C] (F : presheaf X C) 
  (x : X.carrier) : C :=
have G : (nbhds X x)ᵒᵖ ⥤ C, from nbhds_opens_inc_functor X x ⋙ F, 
@colimit (op_Set (nbhds X x).carrier) _ _ _ G (@has_colimit_of_has_colimits C _ H _ _ _) 

/- The product of the sections of a presheaf over a family of open sets. -/
@[hott]
def pi_opens {C : Type u} [category.{v} C] [has_products.{v u w'} C] 
  {I : Set.{w'}} (U : I -> open_sets X) (F : presheaf X C) : C :=   
∏ (λ i : I, F.obj (op (U i)))

/- The product of the sections of a presheaf over the pairwise intersections 
   of a family of open sets.-/
@[hott]
def pi_inters {C : Type u} [category.{v} C] [has_products.{v u w'} C]
  {I : Set.{w'}} (U : I -> open_sets X) (F : presheaf X C) : C :=  
∏ (λ p : ↥(I × I), F.obj (op (open_sets.inter X (U p.1) (U p.2))))

@[hott, reducible]
def left_res {C : Type u} [category.{v} C] [has_products.{v u w'} C]
  {I : Set.{w'}} (U : I -> open_sets X) (F : presheaf X C) : 
  (pi_opens X U F) ⟶ (pi_inters X U F) :=
pi.lift C (λ p : ↥(I × I), pi.π _ p.1 ≫ 
                        F.map (hom_op (opens.inf_le_l X (U p.1) (U p.2))))

@[hott, reducible]
def right_res {C : Type u} [category.{v} C] [has_products.{v u w'} C]
  {I : Set.{w'}} (U : I -> open_sets X) (F : presheaf X C) : 
  (pi_opens X U F) ⟶ (pi_inters X U F) :=
pi.lift C (λ p : ↥I × I, pi.π _ p.2 ≫ 
                       F.map (hom_op (opens.inf_le_r X (U p.1) (U p.2))))

@[hott, reducible]
def res {C : Type u} [category.{v} C] [has_products.{v u u_2} C]
  {I : Set.{u_2}} (U : I -> open_sets X) (F : presheaf X C) :
  (F.obj (op (open_sets.iUnion X U))) ⟶ (pi_opens X U F) :=  
pi.lift C (λ i : I, F.map (hom_op (opens.le_union X U i))) 

@[hott]
def w_res {C : Type u} [category.{v} C] [has_products.{v u u_2} C]
  {I : Set} (U : I -> open_sets X) (F : presheaf X C) :
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
             by rwr <- hom_op_funct (opens.inf_le_l X (U p.1) (U p.2)) _,
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
             by rwr <- hom_op_funct (opens.inf_le_r X (U p.1) (U p.2)) _,
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
def sheaf_condition {C : Type u} [category.{v} C] [has_products.{v u u_2} C] 
  (F : presheaf X C) := Π {I : Set} (U : I -> open_sets X), 
  is_limit (sheaf_condition_equalizer_products.fork X U F)

@[hott]
structure sheaf (C : Type u) [category.{v} C] [has_products.{v u u_2} C] :=
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

/- We construct (pre-)sheaves of sections to a family of sets over open subsets of a 
   topological space that satisfy a (pre-)local predicate. 
   
   We need to take functions with values in sets because otherwise the homomorphisms in 
   the presheaf category will not be sets. Therefore, the presheaf category also will be
   `Set`. -/
open topology

@[hott]
def ss_section (U : open_sets X) (T : X.carrier -> Set) := 
  Π x : U.1.carrier, T ↑x 

@[hott]
def ss_section_Set (U : open_sets X) (T : X.carrier -> Set) : Set := 
  have is_set_ss_section : is_set (ss_section X U T), from is_set_dmap,
  Set.mk (ss_section X U T) is_set_ss_section

@[hott, reducible]
def res_ss_section {U V : open_sets X} (i : U ⟶ V) {T : X.carrier -> Set} :
  ss_section_Set X V T -> ss_section_Set X U T := 
have UV_eq : Π x : U.1.carrier, ↑x = (V.1.map (ss_sset_emb i x)), from 
  assume x, ss_emb_eq i x, 
begin intros f x, rwr UV_eq x, exact f (ss_sset_emb i x) end    

@[hott]
def id_res_section {U : open_sets X} {T : X.carrier -> Set} :
  Π f : ss_section_Set X U T, res_ss_section X (𝟙 U) f = f :=
sorry  

@[hott]
structure prelocal_predicate (T : X.carrier -> Set) :=
  (pred : Π {U : open_sets X}, ss_section X U T → trunctype.{0} -1)
  (res : ∀ {U V : open_sets X} (i : U ⟶ V) (f : ss_section X V T) 
           (h : pred f), pred (res_ss_section X i f))

@[hott]
def subpresheaf_of_sections {T : X.carrier -> Set} (P : prelocal_predicate X T) :
  presheaf X Set :=
begin  
  fapply categories.functor.mk, 
  { intro U, exact ↥{f ∈ ss_section_Set X (unop U) T | P.pred f} },
  { intros U V i f, fapply sigma.mk,  
    { exact res_ss_section X (hom_unop i) f.1 },
    { exact P.res (hom_unop i) f.1 f.2 } },
  { intro U, apply eq_of_homotopy, intro f, 
    fapply sigma_eq, 
    { exact id_res_section X f },
    { apply pathover_of_tr_eq, apply is_prop.elim } },
  { intros U V W i j, hsimp, apply eq_of_homotopy, intro f, 
    fapply sigma_eq, 
    { sorry },
    { apply pathover_of_tr_eq, apply is_prop.elim } }
end  

end hott