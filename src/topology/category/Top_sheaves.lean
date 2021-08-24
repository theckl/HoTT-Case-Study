import topology.basic categories.cat_limits categories.cat_colimits types2

universes v v' u u' w w'
hott_theory

namespace hott
open hott.set hott.subset hott.categories category_theory.limits category_theory.colimits
  categories.opposite hott.sigma hott.is_trunc hott.trunc

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
instance : has_coe ↥(open_sets X) (Subset ↥X) :=
  ⟨λ Y : open_sets X, Y.1⟩

@[hott]
protected def open_sets.inter (U V : open_sets X) : open_sets X :=
have U_is_open : is_open ↥X U, from U.2, 
have V_is_open : is_open ↥X V, from V.2,
have inter_is_open : is_open ↥X (U.1 ∩ V.1), from 
  is_open_inter ↥X U_is_open V_is_open,
⟨U.1 ∩ V.1, inter_is_open⟩  

@[hott, instance]
def open_sets_inter : has_inter (open_sets X) :=
⟨open_sets.inter X⟩    

@[hott]
def open_sets.iUnion {I : Set} (f : I -> open_sets X) : ↥(open_sets X) :=
have U_i_is_open : ∀ i : I, is_open ↥X (f i), from assume i, (f i).2, 
have open_union : is_open ↥X (⋃ᵢ (λ i, (f i).1)), from is_open_iUnion ↥X U_i_is_open,  
⟨⋃ᵢ (λ i, (f i).1), open_union⟩    

@[hott]
instance open_sets_incl_to_hom {U V : open_sets X} : has_coe ↥(U.1 ⊆ V.1) (U ⟶ V) := 
  ⟨λ i : U.1 ⊆ V.1, i⟩ 

@[hott]
def open_sets_hom_to_emb {U V : open_sets X} (i : U ⟶ V) : U.1 -> V.1 :=
  assume x, ⟨x, i x x.2⟩

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
  intro i, 
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
begin  intros U el, exact el.1  end

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
@colimit (op_Set (pred_Set (nbhds X x))) _ _ _ G (@has_colimit_of_has_colimits C _ H _ _ _) 

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

/- Gluing provides an alternative description of the sheaf condition on set-valued presheafs. -/
@[hott]
def is_gluing (F : presheaf X Set) {I : Set} (U : I -> open_sets X) 
  (sf : Π i : I, F.obj (op (U i))) (s : F.obj (op (open_sets.iUnion X U))) : trunctype.{0} -1 :=
prop_resize (to_Prop (∀ i : I, F.map (hom_op (opens.le_union X U i)) s = sf i))

@[hott]
def is_gluing_to_cond (F : presheaf X Set) {I : Set} (U : I -> open_sets X) 
  (sf : Π i : I, F.obj (op (U i))) (s : F.obj (op (open_sets.iUnion X U))) :
  is_gluing X F U sf s -> ∀ i : I, F.map (hom_op (opens.le_union X U i)) s = sf i :=
begin 
  have P : is_prop (∀ i : I, F.map (hom_op (opens.le_union X U i)) s = sf i), from 
    begin apply is_prop_dprod, intro i, apply is_prop.mk, intros p q, exact is_set.elim _ _ end,
  intros ig, 
  exact prop_resize_to_prop ig
end    

@[hott]
def is_compatible {F : presheaf X Set} {I : Set} {U : I -> open_sets X} 
  (sf : Π i : I, F.obj (op (U i))) := ∀ (i j : I), 
    F.map (hom_op (opens.inf_le_l X (U i) (U j))) (sf i) = 
                                         F.map (hom_op (opens.inf_le_r X (U i) (U j))) (sf j)

@[hott]
def cone_res_is_compatible {F : presheaf X Set} {I : Set} {U : I -> open_sets X} 
  {S : cone (parallel_pair (@left_res X _ _ set_has_products _ U F) 
                             (@right_res X _ _ set_has_products _ U F))} :
  ∀ Sf : S.X, @is_compatible X F I U (S.π.app wp_pair.up Sf).1 := 
begin 
  intro Sf, 
  let sf : ↥(@pi_opens X _ _ set_has_products _ U F) := S.π.app wp_pair.up Sf,
  apply all_prod_all, intro p, 
  have H1 : (pi.π (λ (i : ↥I), F.obj (op (U i))) p.fst ≫ 
                    F.map (hom_op (opens.inf_le_l X (U p.fst) (U p.snd)))) =
                          (@left_res X _ _ (set_has_products) _ U F ≫ pi.π _ p), from 
    inverse (pi.lift_π_eq _ _ p), 
  have H2 : (@right_res X _ _ (set_has_products) _ U F ≫ pi.π _ p) =
            (pi.π (λ (i : ↥I), F.obj (op (U i))) p.snd ≫ 
                          F.map (hom_op (opens.inf_le_r X (U p.fst) (U p.snd)))), from
    pi.lift_π_eq _ _ p,                   
  let hl : ↥(@has_hom.hom _ walking_parallel_pair_has_hom wp_pair.up wp_pair.down) :=
    wp_pair_hom.left,
  have H3 : (S.π.app wp_pair.up) ≫ (@left_res X _ _ (set_has_products) _ U F) =
                (𝟙 S.X) ≫ (S.π.app wp_pair.down), from 
    inverse (S.π.naturality hl),
  let hr : ↥(@has_hom.hom _ walking_parallel_pair_has_hom wp_pair.up wp_pair.down) :=
    wp_pair_hom.right,
  have H4 : (S.π.app wp_pair.up) ≫ (@right_res X _ _ (set_has_products) _ U F) =
               (𝟙 S.X) ≫ (S.π.app wp_pair.down), from 
    inverse (S.π.naturality hr), 
  calc (pi.π (λ (i : ↥I), F.obj (op (U i))) p.fst ≫ 
            F.map (hom_op (opens.inf_le_l X (U p.fst) (U p.snd)))) sf =
                  (@left_res X _ _ (set_has_products) _ U F ≫ pi.π _ p) sf : by rwr H1
       ... = ((S.π.app wp_pair.up) ≫ (@left_res X _ _ (set_has_products) _ U F ≫ 
                                                                      pi.π _ p)) Sf : rfl
       ... = (((S.π.app wp_pair.up) ≫ (@left_res X _ _ (set_has_products) _ U F)) ≫ 
                                                                      pi.π _ p) Sf : 
             by rwr precategory.assoc _ _ _
       ... = (((𝟙 S.X) ≫ (S.π.app wp_pair.down)) ≫ pi.π _ p) Sf : by rwr H3 
       ... = ((S.π.app wp_pair.up) ≫ (@right_res X _ _ (set_has_products) _ U F) ≫ 
                                                                      pi.π _ p) Sf : 
             by rwr inverse H4           
       ... = ((S.π.app wp_pair.up) ≫ (@right_res X _ _ (set_has_products) _ U F) ≫ 
                                                                      pi.π _ p) Sf : 
             by rwr inverse (precategory.assoc _ _ _)                                                                                                                                                  
       ... = (@right_res X _ _ (set_has_products) _ U F ≫ pi.π _ p) sf : rfl
       ... = (pi.π (λ (i : ↥I), F.obj (op (U i))) p.snd ≫ 
                      F.map (hom_op (opens.inf_le_r X (U p.fst) (U p.snd)))) sf : by rwr H2    
end                               

@[hott]
def sheaf_condition_unique_gluing (F : presheaf X Set) {I : Set} (U : I -> open_sets X) :=
  ∀ (sf : Π i : I, F.obj (op (U i))), is_compatible X sf -> unique_elem (is_gluing X F U sf) 

@[hott] 
def lift_of_unique_gluing (F : presheaf X Set) {I : Set} (U : I -> open_sets X) :
  sheaf_condition_unique_gluing X F U ->
  ∀ (S : cone (parallel_pair (@left_res X _ _ set_has_products _ U F) 
                             (@right_res X _ _ set_has_products _ U F))), 
  S.X ⟶ (sheaf_condition_equalizer_products.fork X U F).X :=
begin 
  intros sc_ug S Sf, 
  let sf : ↥(@pi_opens X _ _ set_has_products _ U F) := S.π.app wp_pair.up Sf, 
  apply unique_to_elem (is_gluing X F U sf.1), apply sc_ug, 
  exact cone_res_is_compatible X Sf   
end  

@[hott] 
def sheaf_condition_of_unique_gluing (F : presheaf X Set) : 
  (∀ {I : Set} (U : I -> open_sets X), sheaf_condition_unique_gluing X F U) -> 
  @sheaf_condition X _ _ set_has_products F :=
begin 
  intros sc_ug I U, 
  fapply is_limit.mk,
  { apply lift_of_unique_gluing X F U, exact sc_ug U },
  { intro S, 
    have fac_up : (lift_of_unique_gluing X F U (sc_ug U) S) ≫ (res X U F) = S.π.app wp_pair.up, from 
      begin 
        apply eq_of_homotopy, intro Sf,
        let sf : ↥(@pi_opens X _ _ set_has_products _ U F) := S.π.app wp_pair.up Sf, 
        fapply sigma_eq,
        { apply eq_of_homotopy, intro i, 
          let lift_Sf := lift_of_unique_gluing X F U (sc_ug U) S Sf,
          change F.map (hom_op (opens.le_union X U i)) lift_Sf = sf.1 i,
          have gc : ↥(is_gluing X F U sf.1 lift_Sf), from 
            unique_to_pred (is_gluing X F U sf.1) (sc_ug U sf.1 (cone_res_is_compatible X Sf)),
          exact is_gluing_to_cond X F U sf.1 lift_Sf gc i },
        { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
      end,
    intro j, hinduction j, 
    { exact fac_up },
    { let hl : ↥(@has_hom.hom _ walking_parallel_pair_has_hom wp_pair.up wp_pair.down) :=
        wp_pair_hom.left,
      have H : (S.π.app wp_pair.up) ≫ (@left_res X _ _ (set_has_products) _ U F) =
                 (𝟙 S.X) ≫ (S.π.app wp_pair.down), from 
        inverse (S.π.naturality hl),  
      calc lift_of_unique_gluing X F U (sc_ug U) S ≫ (res X U F ≫ 
                                                    @left_res X _ _ (set_has_products) _ U F) =
                 (lift_of_unique_gluing X F U (sc_ug U) S ≫ res X U F) ≫ left_res X U F : 
                 by rwr precategory.assoc _ _ _
           ... = S.π.app wp_pair.up ≫ @left_res X _ _ (set_has_products) _ U F : by rwr fac_up
           ... = (𝟙 S.X) ≫ (S.π.app wp_pair.down) : by rwr H      
           ... = S.π.app wp_pair.down : precategory.id_comp _ } },
  { intros S m m_lift, apply eq_of_homotopy, intro Sf, 
    let sf : ↥(@pi_opens X _ _ set_has_products _ U F) := S.π.app wp_pair.up Sf,
    let lift := lift_of_unique_gluing X F U (sc_ug U) S,
    have H : (sheaf_condition_equalizer_products.fork X U F).π.app wp_pair.up (m Sf) = sf, from 
      homotopy_of_eq (m_lift wp_pair.up) Sf,
    have m_Sf_ig : ↥(is_gluing X F U sf.1 (m Sf)), from 
      prop_to_prop_resize (λ i, homotopy_of_eq (ap sigma.fst H) i),  
    have lift_ig : ↥(is_gluing X F U sf.1 (lift Sf)), from 
      unique_to_pred (is_gluing X F U sf.1) (sc_ug U sf.1 (cone_res_is_compatible X Sf)),  
    let P := unique_to_uniq (is_gluing X F U sf.1) (sc_ug U sf.1 (cone_res_is_compatible X Sf)), 
    exact ap sigma.fst (@is_prop.elim (Σ (a : ↥(F.obj (op (open_sets.iUnion X U)))), 
                               ↥(is_gluing X F U sf.fst a)) P ⟨m Sf, m_Sf_ig⟩ ⟨lift Sf, lift_ig⟩) }
end    

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

@[hott, reducible]
def ss_section (U : open_sets X) (T : X.carrier -> Set) := 
  Π x : U.1, (T x).carrier 

@[hott]
def ss_section_Set (U : open_sets X) (T : X.carrier -> Set) : Set := 
  have is_set_ss_section : is_set (ss_section X U T), from 
    @is_set_dmap (pred_Set U.1) (λ x, T x.1),
  Set.mk (ss_section X U T) is_set_ss_section

@[hott, reducible]
def res_ss_section {U V : open_sets X} (i : U ⟶ V) {T : X.carrier -> Set} :
  ss_section_Set X V T -> ss_section_Set X U T := 
begin intros f x, let y : ↥V.1 := ⟨x.1, i x x.2⟩, exact f y end    

@[hott]
def id_res_section {U : open_sets X} {T : X.carrier -> Set} :
  Π f : ss_section_Set X U T, res_ss_section X (𝟙 U) f = f :=  
begin 
  intro f, apply eq_of_homotopy, intro x, 
  hinduction x with x' pred_x, refl
end  

@[hott]
def comp_res_section {U V W : open_sets X} {T : X.carrier -> Set} 
  (i : U ⟶ V) (j : V ⟶ W) : Π (f : ss_section_Set X W T), 
    res_ss_section X (i ≫ j) f = (res_ss_section X i) (res_ss_section X j f) :=
begin
  intro f, apply eq_of_homotopy, intro x,
  hinduction x with x' pred_x, refl
end   

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
  { intro U, exact pred_Set {f ∈ ss_section_Set X (unop U) T | P.pred f} },
  { intros U V i f, fapply sigma.mk,  
    { exact res_ss_section X (hom_unop i) f.1 },
    { exact P.res (hom_unop i) f.1 f.2 } },
  { intro U, apply eq_of_homotopy, intro f, 
    fapply sigma_eq, 
    { exact id_res_section X f.1 },
    { apply pathover_of_tr_eq, apply is_prop.elim } },
  { intros U V W i j, apply eq_of_homotopy, intro f, 
    fapply sigma_eq, 
    { exact comp_res_section X (hom_unop j) (hom_unop i) f.1 },
    { apply pathover_of_tr_eq, apply is_prop.elim } }
end  

@[hott]
def compat_section {T : X.carrier -> Set} (P : prelocal_predicate X T) {I : Set} 
  {U : I -> open_sets X} (sf : Π i : I, (subpresheaf_of_sections X P).obj (op (U i))) :
  is_compatible X sf -> ∀ (i j : I) (x : X.carrier) (eli : x ∈ (U i).1) (elj : x ∈ (U j).1),
                          (sf i).1 ⟨x, eli⟩ = (sf j).1 ⟨x, elj⟩ :=
begin 
  intros comp i j x eli elj, 
  have el_ij : ↥(x ∈ (open_sets.inter X (U i) (U j))), from ⟨eli, elj⟩,
  have Hi : eli = opens.inf_le_l X (U i) (U j) x el_ij, from is_prop.elim _ _,
  have Hj : elj = opens.inf_le_r X (U i) (U j) x el_ij, from is_prop.elim _ _,
  rwr Hi, rwr Hj, exact homotopy_of_eq (ap sigma.fst (comp i j)) ⟨x, el_ij⟩ 
end   

@[hott]
def glued_section {T : X.carrier -> Set} (P : prelocal_predicate X T) {I : Set} 
  {U : I -> open_sets X} (sf : Π i : I, (subpresheaf_of_sections X P).obj (op (U i))) :
  is_compatible X sf -> (ss_section_Set X (open_sets.iUnion X U) T) :=
begin
  intro is_comp, 
  intro x, let ind_x := Σ i : I, ↑x ∈ (U i).1, 
  have pix : ↥∥ind_x∥, from prop_resize_to_prop x.2,
  let sf_ind_x : ind_x -> T ↑x := λ ix, (sf ix.1).1 ⟨x.1, ix.2⟩,
  have P : is_prop (Σ sx : T ↑x, image sf_ind_x sx), from 
    begin 
      apply is_prop.mk, intros sx_im₁ sx_im₂, fapply sigma_eq, 
      { apply @trunc.elim2 _ (fiber sf_ind_x sx_im₁.1) (fiber sf_ind_x sx_im₂.1) 
                        (sx_im₁.1 = sx_im₂.1) (is_prop.mk (@is_set.elim _ _ _ _)), 
        { intros fib₁ fib₂, rwr <- fib₁.2, rwr <- fib₂.2,
          exact compat_section X P sf is_comp fib₁.1.1 fib₂.1.1 x.1 fib₁.1.2 fib₂.1.2 },
        { exact sx_im₁.2 },
        { exact sx_im₂.2 } },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
    end,
  apply @sigma.fst _ (λ sx : T ↑x, image sf_ind_x sx), 
  apply @untrunc_of_is_trunc _ _ P, 
  apply @trunc_functor _ (Σ (sx : ↥(T ↑x)), ↥(image sf_ind_x sx)) -1 
          (λ ix : ind_x, ⟨sf_ind_x ix, tr (fiber.mk ix (@idp _ (sf_ind_x ix)))⟩),
  exact pix

end    

@[hott]
def res_glued_section {T : X.carrier -> Set} (P : prelocal_predicate X T) {I : Set} 
  {U : I -> open_sets X} (sf : Π i : I, (subpresheaf_of_sections X P).obj (op (U i)))
  (is_comp : is_compatible X sf) : ∀ i : I, 
  res_ss_section X (opens.le_union X U i) (glued_section X P sf is_comp) = (sf i).1 :=
begin 
  intro i, apply eq_of_homotopy, intro x, 
  let xU : ↥(open_sets.iUnion X U) := ⟨x.1, (opens.le_union X U i) x x.2⟩,
  let ind_x := (Σ i : I, ↑xU ∈ (U i).1), let ix : ind_x := ⟨i, x.2⟩,
  let sf_ind_x : ind_x -> T ↑xU := λ ix, (sf ix.1).1 ⟨x.1, ix.2⟩,
  have P : is_prop (Σ sx : T ↑x, image sf_ind_x sx), from --need it a second time
    begin 
      apply is_prop.mk, intros sx_im₁ sx_im₂, fapply sigma_eq, 
      { apply @trunc.elim2 _ (fiber sf_ind_x sx_im₁.1) (fiber sf_ind_x sx_im₂.1) 
                        (sx_im₁.1 = sx_im₂.1) (is_prop.mk (@is_set.elim _ _ _ _)), 
        { intros fib₁ fib₂, rwr <- fib₁.2, rwr <- fib₂.2,
          exact compat_section X P sf is_comp fib₁.1.1 fib₂.1.1 x.1 fib₁.1.2 fib₂.1.2 },
        { exact sx_im₁.2 },
        { exact sx_im₂.2 } },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
    end,
  change (@untrunc_of_is_trunc (Σ (sx : ↥(T ↑xU)), ↥(image sf_ind_x sx)) _ _ _).1 = 
                                                                           (sf i).fst x,
  rwr @is_prop.elim (Σ (sx : ↥(T ↑xU)), ↥(image sf_ind_x sx)) P (@untrunc_of_is_trunc _ _ _ _) 
                   ⟨sf_ind_x ix, tr (fiber.mk ix (@idp _ (sf_ind_x ix)))⟩,
  change ((sf i).1 ⟨x.1, x.2⟩ : T ↑(⟨x.1, x.2⟩ : Σ y : X.carrier, y ∈ (U i).1)) = 
                                                            ((sf i).fst x : T x.1),
  rwr <- sigma.eta x                                                          
end    

@[hott]
def gluings_are_unique {T : X.carrier -> Set} (P : prelocal_predicate X T) {I : Set} 
  {U : I -> open_sets X} (sf : Π i : I, (subpresheaf_of_sections X P).obj (op (U i)))
  (is_comp : is_compatible X sf) : 
  ∀ s₁ s₂ : (subpresheaf_of_sections X P).obj (op (open_sets.iUnion X U)),
    (is_gluing X (subpresheaf_of_sections X P) U sf s₁) -> 
      (is_gluing X (subpresheaf_of_sections X P) U sf s₂) -> s₁ = s₂ :=
begin 
  intros s₁ s₂ gs₁ gs₂, 
  fapply sigma_eq, 
  { apply eq_of_homotopy, intro x, 
    let ind_x := Σ i : I, ↑x ∈ (U i).1, 
    have pix : ↥∥ind_x∥, from prop_resize_to_prop x.2,
    fapply @untrunc_of_is_trunc _ -1,
    apply @trunc_functor ind_x _ -1,
    { intro ix, 
      have p : x = ⟨x.1, opens.le_union X U ix.1 (⟨x.1, ix.2⟩ : (U ix.1).1) ix.2⟩, from 
        begin fapply sigma_eq, refl, apply pathover_of_tr_eq, exact is_prop.elim _ _ end,
      rwr p,  
      change ((subpresheaf_of_sections X P).map (hom_op (opens.le_union X U ix.fst)) s₁).fst 
                                                                              ⟨x.fst, ix.snd⟩ =
             ((subpresheaf_of_sections X P).map (hom_op (opens.le_union X U ix.fst)) s₂).fst 
                                                                              ⟨x.fst, ix.snd⟩,      
      rwr homotopy_of_eq (ap sigma.fst (prop_resize_to_prop gs₁ ix.1)) ⟨x.1, ix.2⟩, 
      rwr homotopy_of_eq (ap sigma.fst (prop_resize_to_prop gs₂ ix.1)) ⟨x.1, ix.2⟩ },
    { exact pix } },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end    

@[hott]
structure local_predicate (T : X.carrier -> Set) extends prelocal_predicate X T :=
  (locality : ∀ {U : open_sets X} (f : ss_section X U T) (w : ∀ x : U.1, 
     ∥ Σ (V : open_sets X) (m : ↑x ∈ V.1) (i : V ⟶ U), pred (res_ss_section X i f) ∥),
     pred f)

/- Universe levels are not determined automatically. -/
@[hott]
def subsheaf_of_sections {T : X.carrier -> Set} (P : local_predicate X T) :
  @sheaf X Set.{max u_1 u_2 u'} Set_category set_has_products.{u_2 (max u_1 u')} :=
begin 
  fapply sheaf.mk,
  { exact subpresheaf_of_sections X P.to_prelocal_predicate },
  { apply sheaf_condition_of_unique_gluing.{u_1 u_2 (max u_1 u')} X 
                                   ((subpresheaf_of_sections X P.to_prelocal_predicate)), 
    intros I U sf is_comp, fapply prod.mk, 
    { fapply sigma.mk, 
      { fapply sigma.mk, --construction of glued section
        { exact glued_section X P.to_prelocal_predicate sf is_comp },
        { apply P.locality, intro x, --glued section satisfies predicate
          let ind_x := Σ i : I, ↑x ∈ (U i).1, 
          have pix : ↥∥ind_x∥, from prop_resize_to_prop x.2,
          apply @trunc_functor ind_x _ -1, 
          { intro ix, 
            fapply sigma.mk, exact (U ix.1),
            fapply sigma.mk, exact ix.2,
            fapply sigma.mk, exact opens.le_union X U ix.1,
            rwr res_glued_section, exact (sf ix.1).2 },
          { exact pix } } },
      { apply prop_to_prop_resize, intro i, fapply sigma_eq, --glued section is gluing
        { exact res_glued_section X P.to_prelocal_predicate sf is_comp i },
        { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } },  
    { apply is_prop.mk,  --glued section is unique
      intros s₁ s₂, fapply sigma_eq, 
      { exact gluings_are_unique X P.to_prelocal_predicate sf is_comp s₁.1 s₂.1 s₁.2 s₂.2 },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }  } 
end   

end hott