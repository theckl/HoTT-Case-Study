import categories.strict_cat          

universes v v' u u' w 
hott_theory

namespace hott
open hott.is_trunc hott.precategories hott.categories.strict

namespace categories                

/- We define the discrete precategory structure on a set, whose morphisms are
   only equalities. 
   
   It is obviously also a category structure, but this is not needed anywhere. 
   
   We start with a synonym for any set indicating that it has a precategory 
   structure. -/
@[hott]
def discrete (A : Set) := A

@[hott, instance]
def discrete_cat_has_hom (A : Set) : has_hom (discrete A) :=
  has_hom.mk (λ a b : A, Set.mk (a = b) 
                                (@is_trunc_succ (a = b) -1 (is_trunc_eq -1 a b)))

@[hott, instance]
def discrete_cat_struct (A : Set) : category_struct (discrete A) :=
  category_struct.mk (λ a : discrete A, @rfl A a)
                     (λ (a b c: discrete A) (f : a ⟶ b) (g : b ⟶ c), f ⬝ g)

@[hott, instance]
def discrete_precategory (A : Set) : is_precat (discrete A) :=
  have ic : Π (a b : discrete A) (f : a ⟶ b), 𝟙 a ≫ f = f, from 
    assume a b f, idp_con f,
  have ci : Π (a b : discrete A) (f : a ⟶ b), f ≫ 𝟙 b = f, from 
    assume a b f, con_idp f,
  have as : Π (a b c d : discrete A) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
             (f ≫ g) ≫ h = f ≫ (g ≫ h), from 
    assume a b c d f g h, con.assoc f g h,
  is_precat.mk ic ci as

@[hott]
def discrete.functor {C : Type u} [is_cat C] {J : Set.{u'}} 
  (f : J -> C) : (discrete J) ⥤ C :=
let map := λ {j₁ j₂ : discrete J} (h : j₁ ⟶ j₂), 
             h ▸[λ k : discrete J, f j₁ ⟶ f k] 𝟙 (f j₁) in 
have map_id : ∀ (j : discrete J), map (𝟙 j) = 𝟙 (f j), from 
  assume j, rfl,
have tr_map_comp : ∀ {j₁ j₂ j₃ : discrete J} (g : j₁ ⟶ j₂) (h : j₂ ⟶ j₃),
  h ▸[λ k : discrete J, f j₁ ⟶ f k] (map g) = (map g) ≫ (map h), from 
  assume j₁ j₂ j₃ g h, by hinduction h; hsimp,    
have map_comp : ∀ {j₁ j₂ j₃ : discrete J} (g : j₁ ⟶ j₂) (h : j₂ ⟶ j₃), 
  map (g ≫ h) = (map g) ≫ (map h), from assume j₁ j₂ j₃ g h,
  calc map (g ≫ h) = ((g ⬝ h) ▸[λ k : discrete J, f j₁ ⟶ f k] 𝟙 (f j₁)) : 
                      rfl
                ... = h ▸ (g ▸[λ k : discrete J, f j₁ ⟶ f k] 𝟙 (f j₁)) : 
                      con_tr g h (𝟙 (f j₁))     
                ... = (map g) ≫ (map h) : tr_map_comp g h,                 
precategories.functor.mk f @map map_id @map_comp

@[hott]
def discrete.nat_trans {C : Type u} [is_cat C] {J : Set.{u'}} 
  {F G : (discrete J) ⥤ C} (app : Π j : J, F.obj j ⟶ G.obj j) :
  F ⟹ G :=  
have natural : ∀ (j j' : J) (f : j ⟶ j'), 
                 (F.map f) ≫ (app j') = (app j) ≫ (G.map f), from                
  begin intros j j' f, hinduction f, hsimp end,
nat_trans.mk app natural  

@[hott, instance]
def discrete_is_strict_cat (A : Set) : is_strict_cat (discrete A) :=
  is_strict_cat.mk (discrete A).struct  


/- An `infinite wedge` has legs to a base node from leaf nodes
   parametrized by arbitrary and possibly infinite sets. 
   
   Better automatisation of the definitions and calculations is desirable.
   The trick in mathlib to define the homomorphisms as an inductive type
   does not work because in HoTT precategories we need to define sets of
   homomorphisms. -/
@[hott]
inductive inf_w_node (A : Set.{u}) : Type u 
  | tip : A -> inf_w_node 
  | base : inf_w_node

@[hott, hsimp]
def inf_wn_ppred {A : Set} (n₁ : inf_w_node A) : ppred n₁ :=
begin 
  fapply ppred.mk,
  { intro n₂, hinduction n₁ with a₁ base, 
    { hinduction n₂ with a₂ base, exact (a₁ = a₂), exact False, },
    { hinduction n₂ with a₂ base, exact False, exact True } },
  { hinduction n₁, hsimp, exact true.intro }
end

@[hott, instance]
def inf_wn_ppred_fam_is_prop {A : Set}: Π (n₁ n₂ : inf_w_node A), 
  is_prop ((inf_wn_ppred n₁).fam n₂) :=
begin 
  intros n₁ n₂, hinduction n₁,
  all_goals {hinduction n₂, all_goals { hsimp, apply_instance } }
end 

@[hott, instance]
def inf_wn_ppred_is_contr {A : Set} (n₁ : inf_w_node A) : 
  is_contr (Σ (n₂ : inf_w_node A), (inf_wn_ppred n₁).fam n₂) :=
begin
  fapply is_contr.mk,  
  { fapply dpair, exact n₁, hinduction n₁, 
    all_goals { hsimp, try {exact true.intro}} },
  { intro own_pair, hinduction own_pair with n₂ ppred₂, 
    hinduction n₁, 
    all_goals { hinduction n₂, all_goals {hinduction ppred₂ }, 
                fapply sigma.sigma_eq, exact idp, 
                apply pathover_idp_of_eq, exact idp } }
end

@[hott, instance]
def inf_wn_is_set (A : Set) : is_set (inf_w_node A) :=
begin 
  apply is_trunc_succ_intro, intros n₁ n₂, 
  fapply @is_trunc_equiv_closed_rev (n₁ = n₂) 
                                    ((inf_wn_ppred n₁).fam n₂),
  exact tot_space_contr_ppmap_id_eqv' (inf_wn_ppred n₁) 
          (can_ppmap _) (inf_wn_ppred_is_contr n₁) n₂, 
  apply_instance
end

@[hott]
def inf_wedge (A : Set.{u}) : Set :=
Set.mk (inf_w_node.{u} A) (inf_wn_is_set.{u u} A)

@[hott]
abbreviation inf_w_tip {A : Set} (a : A) : inf_wedge A := inf_w_node.tip a

@[hott]
def inf_w_base {A : Set} : inf_wedge A := inf_w_node.base A

/- Now we construct the precategory structure on `inf_wedge`. -/
@[hott, hsimp]
def inf_wedge_hom {A : Set} : 
  Π s t : inf_wedge.{u} A, Set.{u} :=
λ s t, match s, t with
       | inf_w_node.tip a₁, inf_w_node.tip a₂ := 
           trunctype.mk (a₁ = a₂) (is_trunc_eq 0 a₁ a₂) --id
       | inf_w_node.tip a, inf_w_node.base A := One_Set --leg arrow
       | inf_w_node.base A, inf_w_node.tip a := Zero_Set
       | inf_w_node.base A, inf_w_node.base _ := One_Set --id
       end 

@[hott, instance]
def inf_wedge_has_hom (A : Set) : 
  has_hom (inf_wedge A) := ⟨inf_wedge_hom⟩

@[hott, instance]
def inf_w_hom_is_prop {A : Set} : Π (s t : inf_wedge A), 
  is_prop (s ⟶ t) :=
λ s t, match s, t with
       | inf_w_node.tip a₁, inf_w_node.tip a₂ := 
           is_trunc_eq -1 a₁ a₂
       | inf_w_node.tip a, inf_w_node.base A := One_is_prop
       | inf_w_node.base A, inf_w_node.tip a := Zero_is_prop
       | inf_w_node.base A, inf_w_node.base _ := One_is_prop
       end  

@[hott]
def inf_w_leg {A : Set} (a : A) : inf_w_tip a ⟶ inf_w_base :=
  One.star

@[hott, hsimp]
def inf_wedge.id {A : Set} : 
  Π (s : inf_wedge A), s ⟶ s :=
λ s, match s with 
     | inf_w_node.tip a := idp
     | inf_w_node.base A := One.star
     end

@[hott, hsimp]
def inf_wedge.comp {A : Set} : 
  Π {s t u : inf_wedge A} (f : s ⟶ t) (g : t ⟶ u), 
  s ⟶ u := 
λ s t u, match s, t, u with
       | inf_w_node.tip a₁, inf_w_node.tip a₂, inf_w_node.tip a₃ := 
         assume f g, f ⬝ g                                              
       | inf_w_node.tip a₁, inf_w_node.tip a₂, inf_w_node.base A := 
         assume f g, begin  hinduction f, exact g end
       | inf_w_node.tip a₁, inf_w_node.base A, inf_w_node.base _ := 
         assume f g, f  
       | inf_w_node.base A, inf_w_node.base _, inf_w_node.base _ := 
         assume f g, f                                                                                  --id ≫ id = id
       | _, inf_w_node.base A, inf_w_node.tip a₂ := 
         assume f g, begin hinduction g end
       | inf_w_node.base A, inf_w_node.tip a₁, _ := 
         assume f g, begin hinduction f end 
       end     

@[hott, instance]
def inf_wedge.cat_struct {A : Set} : 
  category_struct (inf_wedge A) :=
  category_struct.mk inf_wedge.id (@inf_wedge.comp A)   

@[hott, hsimp]
def inf_wedge.id_comp {A : Set} : 
  Π {s t : inf_wedge A} (f : s ⟶ t), 𝟙 s ≫ f = f :=
 begin intros s t f, exact is_prop.elim _ _ end   

@[hott, hsimp]
def inf_wedge.comp_id {A : Set} : 
  Π {s t : inf_wedge A} (f : s ⟶ t), f ≫ 𝟙 t = f :=
begin intros s t f, exact is_prop.elim _ _ end 

@[hott, hsimp]
def inf_wedge.assoc {A : Set} : 
  Π {s t u v : inf_wedge A} (f : s ⟶ t) (g : t ⟶ u)
    (h : u ⟶ v), (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
begin intros s t u v f g h, exact is_prop.elim _ _ end 

@[hott, instance]
def inf_wedge_precat {A : Set} : is_precat (inf_wedge A) :=
  is_precat.mk (@inf_wedge.id_comp A) (@inf_wedge.comp_id A) 
               (@inf_wedge.assoc A)

@[hott]
def Inf_Wedge (A : Set) : Precategory := 
  Precategory.mk (inf_wedge A) inf_wedge_precat 

@[hott, instance]
def Inf_Wedge_is_strict_cat {A : Set} : is_strict_cat (inf_wedge A) :=
  is_strict_cat.mk (inf_wedge A).struct                 

/- [orthogonal_wedge] is the indexing category for pullbacks. 
   We construct it as an instance of the general `infinite wedge`, 
   but try to maintain names to address nodes and legs. -/
@[hott]
inductive ow_node : Type
| left
| upper

/- We need a detailed description which nodes are equal and which not. -/
@[hott]
def own_code : ow_node -> ow_node -> Set :=
λ n₁ n₂, match n₁, n₂ with
         | ow_node.left, ow_node.left := One_Set.{0}
         | ow_node.upper, ow_node.upper := One_Set.{0}
         | _ , _ := Zero_Set.{0}
         end

@[hott]
def refl_own_code : Π (n : ow_node), own_code n n :=
begin intro n, hinduction n, exact One.star, exact One.star end

@[hott]
def own_encode : Π {n₁ n₂ : ow_node}, (n₁ = n₂) -> own_code n₁ n₂ :=
begin intros n₁ n₂ p, hinduction p, exact refl_own_code n₁ end

/- We also need to know that the nodes form a set. -/
@[hott, hsimp]
def own_Two : ow_node -> Two.{0} :=
  λ s, match s with
       | ow_node.left := Two.zero
       | ow_node.upper := Two.one
       end

@[hott, hsimp]
def Two_own : Two.{0} -> ow_node :=
  λ t, match t with
       | Two.zero := ow_node.left
       | Two.one := ow_node.upper
       end

@[hott, instance]
def own_is_set : is_set ow_node :=
  have r_inv : ∀ t : Two.{0}, own_Two (Two_own t) = t, by  
    intro t; hinduction t; hsimp; hsimp,  
  have l_inv : ∀ s : ow_node, Two_own (own_Two s) = s, by
    intro s; hinduction s; hsimp; hsimp,
  have own_eqv_Two: is_equiv own_Two, from
    is_equiv.adjointify own_Two Two_own r_inv l_inv,
  @is_trunc_is_equiv_closed_rev _ _ 0 own_Two own_eqv_Two Two_is_set.{0}

@[hott]
def ow_leg_node : Set :=
Set.mk ow_node own_is_set

@[hott]
def orthogonal_wedge : Set := inf_wedge ow_leg_node

@[hott]
def ow_left : orthogonal_wedge := inf_w_tip ow_node.left

@[hott]
def ow_upper : orthogonal_wedge := inf_w_tip ow_node.upper

@[hott]
def ow_base : orthogonal_wedge := inf_w_base 

@[hott]
def ow_right := inf_w_leg ow_left 

@[hott]
def ow_down := inf_w_leg ow_upper 

@[hott, instance]
def orthogonal_wedge_precat : is_precat orthogonal_wedge :=
  inf_wedge_precat

@[hott, instance]
def orthogonal_wedge_strict_cat : is_strict_cat orthogonal_wedge :=
  Inf_Wedge_is_strict_cat

@[hott]
def Orthogonal_Wedge : strict_Category := 
  strict_Category.mk orthogonal_wedge.carrier orthogonal_wedge_strict_cat

/- The two legs of an orthogonal wedge can be interchanged. -/
@[hott] 
def orthogonal_wedge_iso_hom : Orthogonal_Wedge ⟶ Orthogonal_Wedge :=
begin
  fapply precategories.functor.mk, 
  { intro ow, hinduction ow with n, hinduction n, 
    exact inf_w_tip ow_node.upper, exact inf_w_tip ow_node.left, exact inf_w_base },
  { intros ow₁ ow₂, hinduction ow₁ with n₁, hinduction n₁,
    all_goals { hinduction ow₂ with n₂, hinduction n₂ }, 
    all_goals { intro h, try { solve1 { hsimp } } },
    all_goals { try { solve1 { hinduction (own_encode h) } } },
    all_goals { try { solve1 { hinduction h } } },
    exact inf_w_leg ow_node.upper, exact inf_w_leg ow_node.left, exact One.star },
  { intro ow, hinduction ow with n, hinduction n, all_goals { refl } },
  { intros ow₁ ow₂ ow₃ f g, hinduction ow₁ with n₁, hinduction n₁,
    all_goals { hinduction ow₂ with n₂, hinduction n₂ },
    all_goals { hinduction ow₃ with n₃, hinduction n₃ },
    all_goals { try { solve1 { hsimp} } },
    all_goals { try { solve1 { hinduction (own_encode f) } } },
    all_goals { try { solve1 { hinduction f } } },
    all_goals { try { solve1 { hinduction (own_encode g) } } },
    all_goals { try { solve1 { hinduction g } } } }
end

@[hott] 
def orthogonal_wedge_iso_hom_inv : 
  (orthogonal_wedge_iso_hom ≫ orthogonal_wedge_iso_hom) = 𝟙 Orthogonal_Wedge :=
begin  
  fapply functor_eq,
  { apply eq_of_homotopy, intro ow, hinduction ow with n, hinduction n, 
    all_goals { refl } },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros ow₁ ow₂ h, 
    hinduction ow₁ with n₁, hinduction n₁,
    all_goals { hinduction ow₂ with n₂, hinduction n₂ }, 
    all_goals { try { solve1 { hinduction (own_encode h) } } },
    all_goals { try { solve1 { hinduction h } } },
    all_goals { try { solve1 { exact is_prop.elim _ _ } } } }
end

@[hott] 
def orthogonal_wedge_iso : Orthogonal_Wedge ≅ Orthogonal_Wedge :=
begin
  fapply iso.mk,
  { exact orthogonal_wedge_iso_hom },
  { fapply is_iso.mk,
    { exact orthogonal_wedge_iso_hom },
    { exact orthogonal_wedge_iso_hom_inv },
    { exact orthogonal_wedge_iso_hom_inv } } 
end


/- We define infinite and orthogonal cowedges as opposite 
   precategories of infinite and orthogonal wedges. -/
@[hott]
def inf_cowedge (A : Set) : Set := 
  op_Set (inf_wedge A)

@[hott]
def Inf_Cowedge (A : Set) : Precategory := 
  Precategory.mk (inf_cowedge A) is_precat.opposite

@[hott]
def orthogonal_cowedge := op_Set orthogonal_wedge

@[hott]
def Orthogonal_Cowedge : Precategory := 
  Precategory.mk orthogonal_cowedge is_precat.opposite


/- [walking_parallel_pair] is the indexing category for (co-)equalizers.  -/
@[hott]
inductive wp_pair : Type
| up
| down

@[hott]
inductive wp_pair_hom : Type
| left
| right

/- `wp_pair` and `wp_pair_hom` are sets because they are equivalent to `Two`. -/
@[hott, hsimp]
def wpp_Two : wp_pair -> Two.{0} :=
  λ s, match s with
       | wp_pair.up := Two.zero
       | wp_pair.down := Two.one
       end

@[hott, hsimp]
def wpph_Two : wp_pair_hom -> Two.{0} :=
  λ s, match s with
       | wp_pair_hom.left := Two.zero
       | wp_pair_hom.right := Two.one
       end

@[hott, hsimp]
def Two_wpp : Two.{0} -> wp_pair :=
  λ t, match t with
       | Two.zero := wp_pair.up
       | Two.one := wp_pair.down
       end

@[hott, hsimp]
def Two_wpph : Two.{0} -> wp_pair_hom :=
  λ t, match t with
       | Two.zero := wp_pair_hom.left
       | Two.one := wp_pair_hom.right
       end

@[hott, instance]
def wpp_is_set : is_set wp_pair :=
  have r_inv : ∀ t : Two.{0}, wpp_Two (Two_wpp t) = t, by  
    intro t; hinduction t; hsimp; hsimp,  
  have l_inv : ∀ s : wp_pair, Two_wpp (wpp_Two s) = s, by
    intro s; hinduction s; hsimp; hsimp,
  have wpp_eqv_Two: is_equiv wpp_Two, from
    is_equiv.adjointify wpp_Two Two_wpp r_inv l_inv,
  @is_trunc_is_equiv_closed_rev _ _ 0 wpp_Two wpp_eqv_Two Two_is_set.{0}

@[hott, instance]
def wpph_is_set : is_set wp_pair_hom :=
  have r_inv : ∀ t : Two.{0}, wpph_Two (Two_wpph t) = t, by  
    intro t; hinduction t; hsimp; hsimp,  
  have l_inv : ∀ s : wp_pair_hom, Two_wpph (wpph_Two s) = s, by
    intro s; hinduction s; hsimp; hsimp,
  have wpph_eqv_Two: is_equiv wpph_Two, from
    is_equiv.adjointify wpph_Two Two_wpph r_inv l_inv,
  @is_trunc_is_equiv_closed_rev _ _ 0 wpph_Two wpph_eqv_Two Two_is_set.{0}

@[hott]
def walking_parallel_pair : Set :=
Set.mk wp_pair wpp_is_set

@[hott]
def wpph_Set : Set :=
Set.mk wp_pair_hom wpph_is_set

/- Now we construct the precategory structure on `walking_parallel_pair`. -/
@[hott, hsimp]
def walking_parallel_pair_hom : Π s t : walking_parallel_pair, Set.{0} :=
--begin
--  intros s t, hinduction s with su sd, 
--  { hinduction t with tu td, exact One_Set, exact wpph_Set },
--  { hinduction t with tu td, exact Zero_Set, exact One_Set }
--end
λ s t, match s, t with
       | wp_pair.up, wp_pair.up := One_Set.{0}
       | wp_pair.up, wp_pair.down := wpph_Set
       | wp_pair.down, wp_pair.up := Zero_Set.{0}
       | wp_pair.down, wp_pair.down := One_Set.{0}
       end 

@[hott, instance]
def walking_parallel_pair_has_hom : has_hom walking_parallel_pair := 
  ⟨walking_parallel_pair_hom⟩

@[hott]
def wp_up : walking_parallel_pair := wp_pair.up

@[hott]
def wp_down : walking_parallel_pair := wp_pair.down

@[hott]
def wp_left : wp_up ⟶ wp_down := wp_pair_hom.left

@[hott]
def wp_right : wp_up ⟶ wp_down := wp_pair_hom.right

@[hott]
def walking_parallel_pair.id : Π (s : walking_parallel_pair), s ⟶ s :=
λ s, match s with 
     | wp_pair.up := One.star
     | wp_pair.down := One.star
     end

@[hott, hsimp]
def walking_parallel_pair.comp : Π {s t u : walking_parallel_pair} 
  (f : s ⟶ t) (g : t ⟶ u), s ⟶ u :=
assume s t u f g,     
begin   
  hinduction s,
  { hinduction t,
    { hinduction u,
      { exact walking_parallel_pair.id wp_pair.up },
      { exact g } },
    { hinduction u,
      { hinduction g },
      { exact f } } },
  { hinduction t,
    { hinduction f },
    { hinduction u,
      { hinduction g },
      { exact walking_parallel_pair.id wp_pair.down } } }
end 

@[hott, instance]
def walking_parallel_pair.cat_struct : category_struct walking_parallel_pair :=
  category_struct.mk walking_parallel_pair.id @walking_parallel_pair.comp

@[hott, hsimp]
def wpp_ic : Π {s t : walking_parallel_pair} 
  (f : s ⟶ s) (g : s ⟶ t), f ≫ g = g :=
assume s t f g,
begin
  hinduction s,
  { induction t, 
    { change walking_parallel_pair.id wp_pair.up = g, 
      exact @is_prop.elim _ One_is_prop _ _ },
    { exact rfl } },
  { induction t,
    { hinduction g },
    { change walking_parallel_pair.id wp_pair.down = g, 
      exact @is_prop.elim _ One_is_prop _ _ } }  
end
  
@[hott, hsimp]
def walking_parallel_pair.id_comp : Π {s t : walking_parallel_pair} 
  (f : s ⟶ t), 𝟙 s ≫ f = f :=
assume s t f, wpp_ic (𝟙 s) f    

@[hott, hsimp]
def wpp_ci : Π {s t : walking_parallel_pair} 
  (f : s ⟶ t) (g : t ⟶ t), f ≫ g = f :=
assume s t f g,
begin
  hinduction s,
  { induction t, 
    { change walking_parallel_pair.id wp_pair.up = f, 
      exact @is_prop.elim _ One_is_prop _ _ },
    { exact rfl } },
  { induction t,
    { hinduction f },
    { change walking_parallel_pair.id wp_pair.down = f, 
      exact @is_prop.elim _ One_is_prop _ _ } }  
end

@[hott, hsimp]
def walking_parallel_pair.comp_id : Π {s t : walking_parallel_pair} 
  (f : s ⟶ t), f ≫ 𝟙 t = f :=
assume s t f, wpp_ci f (𝟙 t) 

@[hott, hsimp]
def walking_parallel_pair.assoc : Π {s t u v : walking_parallel_pair} 
  (f : s ⟶ t) (g : t ⟶ u) (h : u ⟶ v), (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
assume s t u v f g h, 
begin 
  hinduction s,
  { hinduction t,
    { hinduction u, 
      { hinduction v, 
        { rwr <-wpp_ic f g },
        { rwr <-wpp_ic f g } },
      { hinduction v, 
        { hinduction h },
        { rwr <-wpp_ic f g } } },
    { hinduction u, 
      { hinduction g },
      { hinduction v, 
        { hinduction h },
        { rwr <-wpp_ci f g } } } },
  { hinduction t,
    { hinduction f },
    { hinduction u, 
      { hinduction g },
      { hinduction v, 
        { hinduction h },
        { rwr <-wpp_ci f g } } } } 
end

@[hott, instance]
def walking_parallel_pair_is_precat : is_precat walking_parallel_pair :=
 is_precat.mk @walking_parallel_pair.id_comp @walking_parallel_pair.comp_id
                @walking_parallel_pair.assoc

@[hott, instance]
def walking_parallel_pair_is_strict_cat : 
  is_strict_cat ↥walking_parallel_pair :=
  @is_strict_cat.mk walking_parallel_pair walking_parallel_pair_is_precat 
                    wpp_is_set

@[hott]
def Walking_parallel_pair : strict_Category :=
  strict_Category.mk walking_parallel_pair walking_parallel_pair_is_strict_cat

end categories

end hott