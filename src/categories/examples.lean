import setalgebra pathover2 set_axioms categories.basic

universes v u v' u' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc hott.is_equiv hott.equiv hott.categories

namespace categories

/- To construct the opposite category, we use the mathlib-trick in [data.opposite]
   that allows the elaborator to do most of the work. -/  
variables {C : Type u}   

@[hott]
def opposite : Type u := C 

notation C `ᵒᵖ`:std.prec.max_plus := @opposite C

namespace opposite

/-- The canonical map `C → Cᵒᵖ`. -/
@[hott]
def op : C → Cᵒᵖ := hott.set.id
/-- The canonical map `Cᵒᵖ → C`. -/
@[hott]
def unop : Cᵒᵖ → C := hott.set.id

@[hott, hsimp]
def op_inj_iff (x y : C) : op x = op y ↔ x = y := iff.rfl

@[hott, hsimp] 
def unop_inj_iff (x y : Cᵒᵖ) : unop x = unop y ↔ x = y := iff.rfl

@[hott, hsimp] 
def op_unop (x : Cᵒᵖ) : op (unop x) = x := rfl

@[hott, hsimp] 
def unop_op (x : C) : unop (op x) = x := rfl

attribute [irreducible] opposite

end opposite

open opposite

@[hott]
instance has_hom.opposite [has_hom.{v} C] : has_hom Cᵒᵖ :=
  has_hom.mk (λ x y, unop y ⟶ unop x) /- Why can't we define a `has_hom` structure with `{}`? -/

/- The opposite of a morphism in `C`. -/
@[hott, reducible]
def hom_op [has_hom.{v} C] {x y : C} (f : x ⟶ y) : op y ⟶ op x := f
/- Given a morphism in `Cᵒᵖ`, we can take the "unopposite" back in `C`. -/
@[hott]
def hom_unop [has_hom.{v} C] {x y : Cᵒᵖ} (f : x ⟶ y) : unop y ⟶ unop x := f

attribute [irreducible] has_hom.opposite /- Why can't you change this name to `has_hom_opp`? -/

@[hott, hsimp] 
def hom_unop_op [has_hom.{v} C] {x y : C} {f : x ⟶ y} : hom_unop (hom_op f) = f := rfl

@[hott, hsimp] 
def hom_op_unop [has_hom.{v} C] {x y : Cᵒᵖ} {f : x ⟶ y} : hom_op (hom_unop f) = f := rfl

/- The opposite precategory. -/
@[hott, instance]
def category_struct.opposite [precategory.{v} C] : category_struct.{v} Cᵒᵖ :=
  category_struct.mk (λ x, hom_op (𝟙 (unop x))) 
                     (λ _ _ _ f g, hom_op (hom_unop g ≫ hom_unop f))

@[hott]
def id_comp_op [precategory.{v} C] : ∀ (x y : Cᵒᵖ) (f : x ⟶ y), 𝟙 x ≫ f = f := 
begin intros x y f, hsimp end
   
@[hott]
def comp_id_op [precategory.{v} C] : ∀ (x y : Cᵒᵖ) (f : x ⟶ y), f ≫ 𝟙 y = f := 
begin intros x y f, hsimp end

@[hott]
def assoc_op [precategory.{v} C] : ∀ (x y z w : Cᵒᵖ) (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ w), 
  (f ≫ g) ≫ h = f ≫ g ≫ h := 
begin 
  intros x y z w f g h, 
  change hom_op (hom_unop h ≫ hom_unop (hom_op (hom_unop g ≫ hom_unop f))) = 
         hom_op (hom_unop (hom_op (hom_unop h ≫ hom_unop g)) ≫ hom_unop f),
  hsimp       
end  

@[hott, instance]
def precategory.opposite [precategory.{v} C] : precategory.{v} Cᵒᵖ :=
  precategory.mk id_comp_op comp_id_op assoc_op                   

@[hott]
def hom_op_funct [precategory.{v} C] {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
  hom_op (f ≫ g) = hom_op g ≫ hom_op f := rfl

/- The opposite category. 
   We show the equivalence by splitting it up in three steps and using that maps from 
   `a = b` are determined by `rfl` if `a` and `b` are allowed to vary freely. -/
@[hott, hsimp]
def id_op_to_id [precategory.{v} C] : Π {a b : Cᵒᵖ}, (a = b) -> (unop a = unop b) :=
  begin intros a b p, hinduction p, exact rfl end  

@[hott, hsimp]
def id_to_id_op [precategory.{v} C] : Π {a b : Cᵒᵖ}, (unop a = unop b) -> (a = b) :=
  assume a b p_op, 
  calc a   = op (unop a) : by hsimp
       ... = op (unop b) : ap op p_op 
       ... = b : op_unop b 

@[hott, instance]
def id_op_eqv_id [precategory.{v} C] : ∀ a b : Cᵒᵖ, is_equiv (@id_op_to_id _ _ a b) :=
  assume a b,
  have rinv : ∀ p_op : unop a = unop b, id_op_to_id (id_to_id_op p_op) = p_op, from  
    begin intro p_op, hsimp, rwr ap_compose', hsimp end, 
  have linv : ∀ p : a = b, id_to_id_op (id_op_to_id p) = p, from 
    begin intro p, hsimp, rwr ap_compose', hsimp end,
  is_equiv.adjointify id_op_to_id id_to_id_op rinv linv   

@[hott, hsimp]
def iso_to_iso_op [precategory.{v} C] : ∀ {a b : Cᵒᵖ}, (unop a ≅ unop b) -> (a ≅ b) :=
begin 
  intros a b i,
  fapply iso.mk, 
    rwr <- op_unop a, rwr <- op_unop b, exact hom_op i.inv,
    rwr <- op_unop a, rwr <- op_unop b, exact hom_op i.hom,
    change hom_op (i.inv ≫ i.hom) = hom_op (𝟙 (unop b)), apply ap hom_op, exact i.r_inv,
    change hom_op (i.hom ≫ i.inv) = hom_op (𝟙 (unop a)), apply ap hom_op, exact i.l_inv   
end

@[hott, hsimp]
def iso_op_to_iso [precategory.{v} C] : ∀ {a b : Cᵒᵖ}, (a ≅ b) -> (unop a ≅ unop b) :=
begin
  intros a b i,
  fapply iso.mk,
    exact hom_unop i.inv,
    exact hom_unop i.hom,
  { rwr <- @hom_unop_op _ _ _ _ (hom_unop i.hom ≫ hom_unop i⁻¹ʰ),  
    rwr <- @hom_unop_op _ _ _ _ (𝟙 (unop b)), exact ap hom_unop (i.r_inv) },
  { rwr <- @hom_unop_op _ _ _ _ (hom_unop i⁻¹ʰ ≫ hom_unop i.hom),  
    rwr <- @hom_unop_op _ _ _ _ (𝟙 (unop a)), exact ap hom_unop (i.l_inv) }
end  

@[hott, instance]
def iso_eqv_iso_op [precategory.{v} C] : ∀ a b : Cᵒᵖ, is_equiv (@iso_to_iso_op _ _ a b) :=
  assume a b,
  have rinv : ∀ h : a ≅ b, iso_to_iso_op (iso_op_to_iso h) = h, from 
    assume h, 
    have hom_eq : (iso_to_iso_op (iso_op_to_iso h)).hom = h.hom, by hsimp, 
    hom_eq_to_iso_eq hom_eq,
  have linv : ∀ h_op : unop a ≅ unop b, iso_op_to_iso (iso_to_iso_op h_op) = h_op, from 
    assume h_op,
    have hom_eq : (iso_op_to_iso (iso_to_iso_op h_op)).hom = h_op.hom, by hsimp,
    hom_eq_to_iso_eq hom_eq,    
  is_equiv.adjointify iso_to_iso_op iso_op_to_iso rinv linv

/- This lemma should belong to [init.path]. Needs function extensionality. -/
@[hott]
def fn_id_rfl {A : Type u} {B : A -> A -> Type v} 
  (f g : ∀ {a b : A}, (a = b) -> B a b) : 
  (∀ a : A, f (@rfl _ a) = g (@rfl _ a)) -> ∀ a b : A, @f a b = @g a b :=
assume fn_rfl_eq,
have fn_hom_eq : ∀ (a b : A) (p : a = b), @f a b p = @g a b p, from 
  begin intros a b p, hinduction p, exact fn_rfl_eq a end,  
assume a b, 
eq_of_homotopy (fn_hom_eq a b) 

@[hott]
def idtoiso_rfl_eq [category.{v} C] : ∀ a : Cᵒᵖ, 
  iso_to_iso_op (idtoiso (id_op_to_id (@rfl _ a))) = 
  idtoiso (@rfl _ a) :=
begin intro a, apply hom_eq_to_iso_eq, change 𝟙 a = 𝟙 a, refl end 

@[hott, instance]
def ideqviso_op [category.{v} C] : ∀ a b : Cᵒᵖ, is_equiv (@idtoiso _ _ a b) :=
  assume a b,
  let f := @id_op_to_id _ _ a b, g := @idtoiso _ _ (unop a) (unop b), 
      h := @iso_to_iso_op _ _ a b in
  have id_optoiso_op : is_equiv (h ∘ g ∘ f), from is_equiv_compose h (g ∘ f), 
  let hgf := λ (a b : Cᵒᵖ) (p : a = b), 
             iso_to_iso_op (idtoiso (id_op_to_id p)) in
  have idtoiso_eq : hgf a b = @idtoiso _ _ a b, from fn_id_rfl _ _ idtoiso_rfl_eq a b,
  begin rwr <- idtoiso_eq; exact id_optoiso_op end

@[hott, instance]
def category.opposite [category.{v} C] : category.{v} Cᵒᵖ :=
  category.mk ideqviso_op 

/- The power set `𝒫 A` of a set `A` is a precategory, with inclusions of 
   subsets as morphisms. -/
@[hott, instance]   
def power_set_has_hom {A : Set.{u}} : has_hom (𝒫 A) :=
  has_hom.mk (λ U V : Subset A, Prop_to_Set (to_Prop (U ⊆ V))) 
  /- I am not sure whether coercions from `Type` to `Prop` and `Prop` to 
    `Set` are a good idea. They may introduce circuitious coercions. -/     

@[hott]
def power_set_unique_hom {A : Set.{u}} {B C : 𝒫 A} (f g : B ⟶ C) : f = g :=
  @is_prop.elim _ (is_prop_subset B C) f g

@[hott, instance]
def power_set_cat_struct {A : Set.{u}} : category_struct (𝒫 A) := 
  category_struct.mk subset_refl subset_trans

@[hott, instance]
def power_set_precat {A : Set.{u}} : precategory (𝒫 A) :=
  have id_comp : ∀ (B C : 𝒫 A) (f : B ⟶ C), 𝟙 B ≫ f = f, from 
    assume B C f, power_set_unique_hom _ _,
  have comp_id : ∀ (B C : 𝒫 A) (f : B ⟶ C), f ≫ 𝟙 C = f, from 
    assume B C f, power_set_unique_hom _ _,
  have assoc   : ∀ (B C D E : 𝒫 A) (f : B ⟶ C) (g : C ⟶ D) (h : D ⟶ E),
                    (f ≫ g) ≫ h = f ≫ (g ≫ h), from
    assume B C D E f g h, power_set_unique_hom _ _,                   
  precategory.mk id_comp comp_id assoc

/- Every subset of a set that is a (small?) precategory is a 
   (full sub-)precategory. -/
@[hott, instance]
def subset_precat_has_hom {A : Set.{u}} [hA : has_hom A] (B : Subset A) :
  has_hom ↥B :=
has_hom.mk (λ x y : ↥↥B, @has_hom.hom _ hA x y)  

@[hott, instance]
def subset_precat_cat_struct {A : Set.{u}} [hA : category_struct A] 
  (B : Subset A) : category_struct ↥B :=
category_struct.mk (λ b : ↥↥B, @category_struct.id _ hA ↑b)
  (λ (b c d : ↥↥B) (f : b ⟶ c) (g : c ⟶ d), 
        @category_struct.comp _ hA ↑b ↑c ↑d f g)
                    
@[hott, instance]
def subset_precat_precat {A : Set.{u}} [hA : precategory A] 
  (B : Subset A) : precategory ↥B :=
precategory.mk (λ (b c : ↥↥B) (f : b ⟶ c), precategory.id_comp f) 
               (λ (b c : ↥↥B) (f : b ⟶ c), precategory.comp_id f) 
               (λ (b c d e: ↥↥B) (f : b ⟶ c) (g : c ⟶ d) (h : d ⟶ e), 
                  precategory.assoc f g h)    

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
def discrete.functor {C : Type u} [category C] {J : Set} 
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
def discrete.nat_trans {C : Type u} [category C] {J : Set} 
  (F G : (discrete J) ⥤ C) (app : Π j : J, F.obj j ⟶ G.obj j) :
  F ⟹ G :=  
have natural : ∀ (j j' : J) (f : j ⟶ j'), 
                 (F.map f) ≫ (app j') = (app j) ≫ (G.map f), from                
  begin intros j j' f, hinduction f, hsimp end,
nat_trans.mk app natural  

/- [walking_parallel_pair] is the indexing category for (co-)equalizers. 

   Better automatisation of the definitions and calculations is desirable.
   The trick in mathlib to define the homomorphisms as an inductive type
   does not work because in HoTT precategories we need to define sets of
   homomorphisms. -/
@[hott]
inductive wp_pair : Type u
| up
| down

/- `wp_pair` is a set because it is equivalent to `Two`. -/
@[hott, hsimp]
def wpp_Two : wp_pair.{u} -> Two.{u} :=
  λ s, match s with
       | wp_pair.up := Two.zero
       | wp_pair.down := Two.one
       end

@[hott, hsimp]
def Two_wpp : Two.{u} -> wp_pair.{u} :=
  λ t, match t with
       | Two.zero := wp_pair.up
       | Two.one := wp_pair.down
       end

@[hott, instance]
def wpp_is_set : is_set wp_pair.{u} :=
  have r_inv : ∀ t : Two, wpp_Two (Two_wpp t) = t, by  
    intro t; hinduction t; hsimp; hsimp,  
  have l_inv : ∀ s : wp_pair, Two_wpp (wpp_Two s) = s, by
    intro s; hinduction s; hsimp; hsimp,
  have wpp_eqv_Two: is_equiv wpp_Two, from
    adjointify wpp_Two Two_wpp r_inv l_inv,
  @is_trunc_is_equiv_closed_rev _ _ 0 wpp_Two wpp_eqv_Two Two_is_set

@[hott]
def walking_parallel_pair : Set.{u} :=
Set.mk wp_pair wpp_is_set

/- Now we construct the precategory structure on `walking__parallel_pair`. -/
@[hott, hsimp]
def walking_parallel_pair_hom : Π s t : walking_parallel_pair.{u}, Set.{u} :=
λ s t, match s, t with
       | wp_pair.up, wp_pair.up := One_Set
       | wp_pair.up, wp_pair.down := Two_Set
       | wp_pair.down, wp_pair.up := Zero_Set
       | wp_pair.down, wp_pair.down := One_Set
       end 

@[hott, instance]
def walking_parallel_pair_has_hom : has_hom walking_parallel_pair := 
  ⟨walking_parallel_pair_hom⟩

@[hott]
def walking_parallel_pair.id : Π (s : walking_parallel_pair.{u}), s ⟶ s :=
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

/- `Set.{u}` is a category - the category of `u`-small sets. -/
@[hott, instance]
def set_has_hom : has_hom Set.{u} :=
  has_hom.mk (λ A B : Set.{u}, Set.mk (A -> B) (@is_set_map A B))

@[hott, instance]
def set_cat_struct : category_struct Set.{u} :=
  category_struct.mk (λ A : Set.{u}, id_map A)
                     (λ (A B C: Set.{u}) (f : A ⟶ B) (g : B ⟶ C), g ∘ f)  

@[hott, instance]
def Set_precategory : precategory Set.{u} :=
  have ic : Π (A B : Set.{u}) (f : A ⟶ B), 𝟙 A ≫ f = f, from 
    assume A B f, by refl,
  have ci : Π (A B : Set.{u}) (f : A ⟶ B), f ≫ 𝟙 B = f, from 
    assume A B f, by refl,
  have as : Π (A B C D : Set.{u}) (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D),
             (f ≫ g) ≫ h = f ≫ (g ≫ h), from 
    assume A B C D f g h, by refl,
  precategory.mk ic ci as

@[hott]
def Set_iso_eqv_bijective : Π (A B : Set.{u}), (A ≅ B) ≃ (bijection A B) :=
  assume A B,
  have is_inv : Π i : A ≅ B, is_set_inverse_of i.hom i.inv, from assume i,
    have i_l_inv : is_set_left_inverse_of i.hom i.inv, from 
      assume a, homotopy_of_eq i.l_inv a,
    have i_r_inv : is_set_right_inverse_of i.hom i.inv, from 
      assume a, homotopy_of_eq i.r_inv a,
    is_set_inverse_of.mk i_r_inv i_l_inv,
  let iso_to_bij := λ i : A ≅ B, has_inverse_to_bijection i.hom i.inv (is_inv i) in
      /- bij_to_iso := λ f : bijection A B, iso.mk f.map _ _ _ in -/
  sorry

@[hott, instance]
def Set_category : category Set.{u} :=
  have ideqviso : ∀ A B : Set.{u}, is_equiv (@idtoiso _ _ A B), from assume A B,
    let iso_eqv_id := (Set_iso_eqv_bijective A B) ⬝e (@set_eq_equiv_bij A B)⁻¹ᵉ in
    have p : @idtoiso _ _ A B = iso_eqv_id⁻¹ᶠ, from sorry,
    have eqv : is_equiv iso_eqv_id⁻¹ᶠ, from is_equiv_to_inv iso_eqv_id,
    p⁻¹ ▸ eqv,
  category.mk ideqviso  

end categories

end hott