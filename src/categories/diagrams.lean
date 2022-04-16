import sets.algebra init2 sets.axioms sets.theories categories.basic categories.examples

universes v v' u u' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc hott.is_equiv hott.equiv hott.categories 

namespace categories

/- Diagrams are small precategories, that is precategories whose type of objects is a
   set. In [HoTT-Book,Ch.9.6] they are called `strict categories`. We don't insist on 
   the precategories being categories, becuase we allow diagrams with loops, that is 
   cycles of homomorphisms that always yield the identity homomorphism when composed. 
  
   Diagrams together with functors between them form a category. In particular, 
   equality of functors between diagrams is unique. -/
@[hott]
structure small_precategory :=
  (obj : Set.{u})
  (precat : precategory.{v} obj)

attribute [instance] small_precategory.precat

@[hott]
def small_precat_eq {D₁ D₂ : small_precategory} : Π (Pₒ : D₁.obj = D₂.obj) 
  (Pₕ : Π a b : D₁.obj, (a ⟶ b) = (Pₒ ▸[(λ (A : Set), A.carrier)] a ⟶ 
                                                 Pₒ ▸[(λ (A : Set), A.carrier)] b)), 
  (Π a : D₁.obj, (Pₕ a a) ▸ 𝟙 a = 𝟙 (Pₒ ▸ a)) -> 
  (Π (a b c : D₁.obj) (f : a ⟶ b) (g : b ⟶ c), (Pₕ a c) ▸ (f ≫ g) = 
                            ((Pₕ a b) ▸ f) ≫ ((Pₕ b c) ▸ g)) -> D₁ = D₂ :=
begin
  hinduction D₁ with obj₁ precat₁, hinduction D₂ with obj₂ precat₂, hsimp, 
  intros Pₒ Pₕ id_eq comp_eq, 
  hinduction Pₒ, fapply apd011 small_precategory.mk, 
  { exact idp },
  { apply pathover_idp_of_eq, 
    hinduction precat₁ with cat_struct₁ id_comp₁ comp_id₁ comp_assoc₁, 
    hinduction precat₂ with cat_struct₂ id_comp₂ comp_id₂ comp_assoc₂,
    fapply apd01111' (@precategory.mk obj₁), 
    { hinduction cat_struct₁ with has_hom₁ id₁ comp₁, 
      hinduction cat_struct₂ with has_hom₂ id₂ comp₂,
      hinduction has_hom₁ with hom₁, hinduction has_hom₂ with hom₂, 
      fapply apd0111' (@category_struct.mk obj₁),
      { apply ap has_hom.mk, apply eq_of_homotopy2, intros a b, exact Pₕ a b },
      { apply pathover_ap,         
        apply pathover_of_tr_eq, apply eq_of_homotopy, intro a, rwr tr_fn_tr_eval,  
        rwr <- ap100_tr (eq_of_homotopy2 (λ (a b : ↥obj₁), Pₕ a b)) (id₁ a), 
        rwr ap100_eq_of_hty2_inv, exact id_eq a },
      { apply pathover_ap,         
        apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b c, rwr tr_fn_tr_eval,
        apply eq_of_homotopy2, intros f g,   
        rwr <- ap100_tr_comp (eq_of_homotopy2 (λ (a b : ↥obj₁), Pₕ a b)) (@comp₁ a) f g, 
        rwr ap100_eq_of_hty2_inv, rwr comp_eq a b c, rwr tr_inv_tr, rwr tr_inv_tr } },
    { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b f, exact is_set.elim _ _ },
    { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b f, exact is_set.elim _ _ },
    { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b c, 
      apply eq_of_homotopy3, intros d f g, apply eq_of_homotopy, intro h, 
      exact is_set.elim _ _ } }
end  

@[hott, instance]
def functors_of_small_precat_is_set (D₁ D₂ : small_precategory) : 
  is_set (D₁.obj ⥤ D₂.obj) :=
begin 
  fapply is_set.mk, intros F G p q, 
  rwr <- functor_eq_eta D₁.obj D₂.obj p, rwr <- functor_eq_eta D₁.obj D₂.obj q, 
  fapply apd011 (functor_eq D₁.obj D₂.obj), 
  { apply is_set.elim _ _, exact is_set_map },
  { apply pathover_of_tr_eq, 
    apply @set_po_eq (D₁.obj -> D₂.obj) 
                     (λ f, Set.mk (Π (x y : D₁.obj), (x ⟶ y) → (f x ⟶ f y)) _)
                     _ _ (ap functor.obj q) _ _ _ _, 
    change is_trunc 0 (Π (x : D₁.obj), Set.mk (Π (y : D₁.obj), (x ⟶ y) → (f x ⟶ f y)) _), 
    apply is_set_dmap, 
    change is_trunc 0 (Π (y : D₁.obj), Set.mk ((x ⟶ y) → (f x ⟶ f y)) _),
    apply is_set_dmap, exact is_set_map }
end    

@[hott, instance]
def small_precat_has_hom : has_hom (small_precategory) :=
  has_hom.mk (λ D₁ D₂ : small_precategory, Set.mk (D₁.obj ⥤ D₂.obj) 
                                            (functors_of_small_precat_is_set D₁ D₂))     

@[hott, instance]
def small_precat_cat_str : category_struct small_precategory :=
  category_struct.mk (λ D, id_functor D.obj) (λ D₁ D₂ D₃ F G, functor_comp F G)

@[hott, instance]
def small_precat_precat : precategory small_precategory :=
precategory.mk (λ D₁ D₂ F, funct_id_comp F) 
               (λ D₁ D₂ F, funct_comp_id F) 
               (λ D₁ D₂ D₃ D₄ F G H, funct_comp_assoc F G H)

@[hott]
def small_precat_iso_to_obj_iso : 
  Π {D₁ D₂ : small_precategory}, (D₁ ≅ D₂) -> (D₁.obj ≅ D₂.obj) :=
assume D₁ D₂ iD, iso.mk iD.hom.obj  iD.inv.obj (ap functor.obj iD.r_inv) 
                                               (ap functor.obj iD.l_inv)

@[hott]
def small_precat_iso_to_hom_iso : Π {D₁ D₂ : small_precategory} (iD : D₁ ≅ D₂), 
  Π (a b : D₁.obj), (a ⟶ b) ≅ (functor.obj iD.hom a ⟶ functor.obj iD.hom b) :=
begin
  intros D₁ D₂ iD a b, 
  fapply iso.mk, 
  { exact λ f : a ⟶ b, functor.map iD.hom f },
  { let F := λ g : functor.obj iD.hom a ⟶ functor.obj iD.hom b, functor.map iD.inv g,
    have H : Π a : D₁.obj, iD⁻¹ʰ.obj (functor.obj iD.hom a) = a, from 
    begin 
      intro a, change functor.obj (iD.hom ≫ iD.inv) a = a,
      rwr ap functor.obj iD.l_inv 
    end,                                      
    rwr H at F, rwr H at F, exact F },
  { apply eq_of_homotopy, intro f, change iD.hom.map _ = f, sorry },
  { sorry}
end

@[hott]
def small_precat_isotoid : Π {D₁ D₂ : small_precategory}, (D₁ ≅ D₂) -> (D₁ = D₂) :=
begin  
  intros D₁ D₂ iD, fapply small_precat_eq, 
  { exact Set_isotoid (small_precat_iso_to_obj_iso iD) },
  { intros a b, rwr Set_isotoid_eq_hom (small_precat_iso_to_obj_iso iD) a, 
    rwr Set_isotoid_eq_hom (small_precat_iso_to_obj_iso iD) b,
    exact Set_isotoid (small_precat_iso_to_hom_iso iD a b) },
  { sorry },
  { sorry }
end    

@[hott, instance]
def small_precat_cat : category small_precategory :=
begin
  apply category.mk, intros D₁ D₂, fapply adjointify,
  { exact small_precat_isotoid },
  { intro b, change small_precat_isotoid b ▸ (id_is_iso D₁) = b, apply hom_eq_to_iso_eq,
    rwr fn2_tr_tr_ev (@iso.hom _ _), 
    change small_precat_isotoid b ▸[λ D : small_precategory, D₁.obj ⥤ D.obj] 
                                                                    id_functor D₁.obj = _,  
    fapply functor_eq, 
    { change (λ D : small_precategory, @functor.obj D₁.obj D.obj _ _) D₂ 
                (small_precat_isotoid b ▸[λ D : small_precategory, D₁.obj ⥤ D.obj] 
                id_functor (D₁.obj)) = _,
      rwr fn_tr_tr_ev (λ D : small_precategory, @functor.obj D₁.obj D.obj _ _), 
      change small_precat_isotoid b ▸[λ D: small_precategory, D₁.obj -> D.obj] 
                                                (id_functor ↥(D₁.obj)).obj = b.hom.obj,
      sorry },
    { sorry } },
  { sorry }
end                 


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
def discrete_precategory (A : Set) : precategory (discrete A) :=
  have ic : Π (a b : discrete A) (f : a ⟶ b), 𝟙 a ≫ f = f, from 
    assume a b f, idp_con f,
  have ci : Π (a b : discrete A) (f : a ⟶ b), f ≫ 𝟙 b = f, from 
    assume a b f, con_idp f,
  have as : Π (a b c d : discrete A) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
             (f ≫ g) ≫ h = f ≫ (g ≫ h), from 
    assume a b c d f g h, con.assoc f g h,
  precategory.mk ic ci as

@[hott]
def discrete.functor {C : Type u} [category.{v} C] {J : Set.{u'}} 
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
functor.mk f @map map_id @map_comp

@[hott]
def discrete.nat_trans {C : Type u} [category.{v} C] {J : Set.{u'}} 
  {F G : (discrete J) ⥤ C} (app : Π j : J, F.obj j ⟶ G.obj j) :
  F ⟹ G :=  
have natural : ∀ (j j' : J) (f : j ⟶ j'), 
                 (F.map f) ≫ (app j') = (app j) ≫ (G.map f), from                
  begin intros j j' f, hinduction f, hsimp end,
nat_trans.mk app natural  

/- [orthogonal_wedge] is the indexing category for pullbacks. 

   Better automatisation of the definitions and calculations is desirable.
   The trick in mathlib to define the homomorphisms as an inductive type
   does not work because in HoTT precategories we need to define sets of
   homomorphisms. -/
@[hott]
inductive ow_node : Type u
| left
| base
| upper

@[hott]
def own_code : ow_node -> ow_node -> Prop :=
begin 
  intros n₁ n₂, hinduction n₁, 
  { hinduction n₂, exact True, exact False, exact False },
  { hinduction n₂, exact False, exact True, exact False },
  { hinduction n₂, exact False, exact False, exact True } 
end

@[hott]
def own_code_refl : Π n : ow_node, own_code n n :=
begin intro n, hinduction n, all_goals { hsimp, exact true.intro } end 

@[hott]
def encode : Π {n₁ n₂ : ow_node}, n₁ = n₂ -> own_code n₁ n₂ :=
  assume n₁ n₂ p, p ▸[λ n, own_code n₁ n] (own_code_refl n₁)

@[hott]
def decode : Π {n₁ n₂ : ow_node}, own_code n₁ n₂ -> n₁ = n₂ :=
begin  
  intros n₁ n₂ ownc, hinduction n₁,
  { hinduction n₂, refl, hinduction ownc, hinduction ownc },
  { hinduction n₂, hinduction ownc, refl, hinduction ownc },
  { hinduction n₂, hinduction ownc, hinduction ownc, refl }
end  

@[hott]
def own_code_is_contr_to_refl  (n₁ : ow_node) : 
  Π (n_code : Σ (n₂ : ow_node), own_code n₁ n₂), n_code = ⟨n₁, own_code_refl n₁⟩ :=
begin 
  intro n_code, fapply sigma.sigma_eq, 
  { exact (decode n_code.2)⁻¹ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott, instance]
def own_code_is_contr (n₁ : ow_node) : is_contr (Σ (n₂ : ow_node), own_code n₁ n₂) :=
  is_contr.mk _ (λ n_code, (own_code_is_contr_to_refl n₁ n_code)⁻¹)  

@[hott, instance]
def own_is_set : is_set ow_node :=
begin
  apply is_trunc_succ_intro, intros n₁ n₂, 
    have eqv : (n₁ = n₂) ≃ (own_code n₁ n₂), from 
    equiv.mk _ (tot_space_contr_id_equiv ⟨(λ n, own_code n₁ n), own_code_refl n₁⟩ 
                                         (own_code_is_contr n₁) n₂), 
  exact is_trunc_equiv_closed_rev -1 eqv (own_code n₁ n₂).struct
end

@[hott]
def orthogonal_wedge : Set :=
Set.mk ow_node.{u} own_is_set.{u u}

/- Now we construct the precategory structure on `orthogonal_wedge`. -/
@[hott, hsimp]
def orthogonal_wedge_hom : Π s t : orthogonal_wedge.{u}, Set.{u} :=
λ s t, match s, t with
       | ow_node.left, ow_node.left := One_Set --id
       | ow_node.left, ow_node.base := One_Set --right arrow
       | ow_node.left, ow_node.upper := Zero_Set
       | ow_node.base, ow_node.left := Zero_Set
       | ow_node.base, ow_node.base := One_Set --id
       | ow_node.base, ow_node.upper := Zero_Set
       | ow_node.upper, ow_node.left := Zero_Set
       | ow_node.upper, ow_node.base := One_Set --down arrow
       | ow_node.upper, ow_node.upper := One_Set --id
       end 

@[hott, instance]
def orthogonal_wedge_has_hom : has_hom orthogonal_wedge := 
  ⟨orthogonal_wedge_hom⟩

@[hott, instance]
def ow_hom_is_prop : Π (s t : orthogonal_wedge), is_prop (s ⟶ t) :=
λ s t, match s, t with
       | ow_node.left, ow_node.left := One_is_prop 
       | ow_node.left, ow_node.base := One_is_prop
       | ow_node.left, ow_node.upper := Zero_is_prop
       | ow_node.base, ow_node.left := Zero_is_prop
       | ow_node.base, ow_node.base := One_is_prop
       | ow_node.base, ow_node.upper := Zero_is_prop
       | ow_node.upper, ow_node.left := Zero_is_prop
       | ow_node.upper, ow_node.base := One_is_prop
       | ow_node.upper, ow_node.upper := One_is_prop
       end  

@[hott]
def ow_left : orthogonal_wedge := ow_node.left

@[hott]
def ow_base : orthogonal_wedge := ow_node.base

@[hott]
def ow_upper : orthogonal_wedge := ow_node.upper

@[hott]
def ow_right : ow_left ⟶ ow_base := One.star

@[hott]
def ow_down : ow_upper ⟶ ow_base := One.star

@[hott]
def orthogonal_wedge.id : Π (s : orthogonal_wedge), s ⟶ s :=
λ s, match s with 
     | ow_node.left := One.star
     | ow_node.base := One.star
     | ow_node.upper := One.star
     end

@[hott, hsimp]
def orthogonal_wedge.comp : Π {s t u : orthogonal_wedge} 
  (f : s ⟶ t) (g : t ⟶ u), s ⟶ u := 
λ s t u, match s, t, u with
       | ow_node.left, ow_node.left, ow_node.left := assume f g, orthogonal_wedge.id ow_node.left 
                                                                                  --id ≫ id = id
       | ow_node.left, ow_node.left, ow_node.base := assume f g, g --id ≫ right = right
       | ow_node.left, ow_node.base, ow_node.base := assume f g, f --right ≫ id = right 
       | ow_node.base, ow_node.base, ow_node.base := assume f g, orthogonal_wedge.id ow_node.base
                                                                                  --id ≫ id = id
       | ow_node.upper, ow_node.base, ow_node.base := assume f g, f --down ≫ id = down
       | ow_node.upper, ow_node.upper, ow_node.base := assume f g, g --id ≫ down = down
       | ow_node.upper, ow_node.upper, ow_node.upper := assume f g, orthogonal_wedge.id ow_node.upper 
                                                                                 --id ≫ id = id
       | ow_node.left, ow_node.upper, _ := assume f g, begin hinduction f end --empty cases
       | ow_node.base, ow_node.left, _ := assume f g, begin hinduction f end 
       | ow_node.base, ow_node.upper, _ := assume f g, begin hinduction f end 
       | ow_node.upper, ow_node.left, _ := assume f g, begin hinduction f end 
       | _, ow_node.left, ow_node.upper := assume f g, begin hinduction g end 
       | _, ow_node.base, ow_node.left := assume f g, begin hinduction g end 
       | _, ow_node.base, ow_node.upper := assume f g, begin hinduction g end 
       | _, ow_node.upper, ow_node.left := assume f g, begin hinduction g end                                                                         
       end     

@[hott, instance]
def orthogonal_wedge.cat_struct : category_struct orthogonal_wedge :=
  category_struct.mk orthogonal_wedge.id @orthogonal_wedge.comp  

@[hott, hsimp]
def orthogonal_wedge.id_comp : Π {s t : orthogonal_wedge} 
  (f : s ⟶ t), 𝟙 s ≫ f = f :=
 begin intros s t f, exact is_prop.elim _ _ end   

@[hott, hsimp]
def orthogonal_wedge.comp_id : Π {s t : orthogonal_wedge} 
  (f : s ⟶ t), f ≫ 𝟙 t = f :=
begin intros s t f, exact is_prop.elim _ _ end 

@[hott, hsimp]
def orthogonal_wedge.assoc : Π {s t u v : orthogonal_wedge} 
  (f : s ⟶ t) (g : t ⟶ u) (h : u ⟶ v), (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
begin intros s t u v f g h, exact is_prop.elim _ _ end 

@[hott, instance]
def orthogonal_wedge_precategory : precategory orthogonal_wedge :=
  precategory.mk @orthogonal_wedge.id_comp @orthogonal_wedge.comp_id @orthogonal_wedge.assoc


/- [walking_parallel_pair] is the indexing category for (co-)equalizers.  -/
@[hott]
inductive wp_pair : Type u
| up
| down

@[hott]
inductive wp_pair_hom : Type u
| left
| right

/- `wp_pair` and `wp_pair_hom` are sets because they are equivalent to `Two`. -/
@[hott, hsimp]
def wpp_Two : wp_pair.{u} -> Two.{u} :=
  λ s, match s with
       | wp_pair.up := Two.zero
       | wp_pair.down := Two.one
       end

@[hott, hsimp]
def wpph_Two : wp_pair_hom.{u} -> Two.{u} :=
  λ s, match s with
       | wp_pair_hom.left := Two.zero
       | wp_pair_hom.right := Two.one
       end

@[hott, hsimp]
def Two_wpp : Two.{u} -> wp_pair.{u} :=
  λ t, match t with
       | Two.zero := wp_pair.up
       | Two.one := wp_pair.down
       end

@[hott, hsimp]
def Two_wpph : Two.{u} -> wp_pair_hom.{u} :=
  λ t, match t with
       | Two.zero := wp_pair_hom.left
       | Two.one := wp_pair_hom.right
       end

@[hott, instance]
def wpp_is_set : is_set wp_pair.{u} :=
  have r_inv : ∀ t : Two, wpp_Two (Two_wpp t) = t, by  
    intro t; hinduction t; hsimp; hsimp,  
  have l_inv : ∀ s : wp_pair, Two_wpp (wpp_Two s) = s, by
    intro s; hinduction s; hsimp; hsimp,
  have wpp_eqv_Two: is_equiv wpp_Two, from
    adjointify wpp_Two Two_wpp r_inv l_inv,
  @is_trunc_is_equiv_closed_rev.{u u} _ _ 0 wpp_Two wpp_eqv_Two Two_is_set

@[hott, instance]
def wpph_is_set : is_set wp_pair_hom.{u} :=
  have r_inv : ∀ t : Two, wpph_Two (Two_wpph t) = t, by  
    intro t; hinduction t; hsimp; hsimp,  
  have l_inv : ∀ s : wp_pair_hom, Two_wpph (wpph_Two s) = s, by
    intro s; hinduction s; hsimp; hsimp,
  have wpph_eqv_Two: is_equiv wpph_Two, from
    adjointify wpph_Two Two_wpph r_inv l_inv,
  @is_trunc_is_equiv_closed_rev.{u u} _ _ 0 wpph_Two wpph_eqv_Two Two_is_set

@[hott]
def walking_parallel_pair : Set :=
Set.mk wp_pair.{u} wpp_is_set.{u u}

@[hott]
def wpph_Set : Set :=
Set.mk wp_pair_hom.{u} wpph_is_set.{u u}

/- Now we construct the precategory structure on `walking_parallel_pair`. -/
@[hott, hsimp]
def walking_parallel_pair_hom : Π s t : walking_parallel_pair.{u}, Set.{u} :=
λ s t, match s, t with
       | wp_pair.up, wp_pair.up := One_Set
       | wp_pair.up, wp_pair.down := wpph_Set
       | wp_pair.down, wp_pair.up := Zero_Set
       | wp_pair.down, wp_pair.down := One_Set
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
def walking_parallel_pair_precategory : precategory walking_parallel_pair :=
 precategory.mk @walking_parallel_pair.id_comp @walking_parallel_pair.comp_id
                @walking_parallel_pair.assoc

end categories

end hott