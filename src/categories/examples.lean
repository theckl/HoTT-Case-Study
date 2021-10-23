import sets.setalgebra init2 sets.set_axioms categories.basic

universes v v' u u' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc hott.is_equiv hott.equiv hott.categories 

namespace categories

set_option pp.universes false

/- To construct the opposite category, we use the mathlib-trick in [data.opposite]
   that allows the elaborator to do most of the work. -/  
variables {C : Type u} {D : Type u'}  

@[hott]
def opposite : Type u := C 

notation C `ᵒᵖ`:std.prec.max_plus := @opposite C

@[hott]
def op_Set (C : Set.{u}) : Set :=
  Set.mk Cᵒᵖ (C.struct)

namespace opposite

/-- The canonical map `C → Cᵒᵖ`. -/
@[hott]
def op : C → Cᵒᵖ := id
/-- The canonical map `Cᵒᵖ → C`. -/
@[hott]
def unop : Cᵒᵖ → C := id

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

@[hott]
def opposite_functor [precategory.{v} C] [precategory.{v'} D] : (C ⥤ D) -> (Cᵒᵖ ⥤ Dᵒᵖ) :=
begin
  intro F, fapply functor.mk,
  { intro c, exact op (F.obj (unop c)) },
  { intros x y f, apply hom_op, exact F.map (hom_unop f) },
  { intro x, hsimp, refl },
  { intros x y z f g, hsimp, refl }
end

/- The power set `𝒫 A` of a set `A` is a precategory, with inclusions of 
   subsets as morphisms. -/
@[hott, instance]   
def power_set_has_hom {A : Set} : has_hom (𝒫 A) :=
  has_hom.mk (λ U V : Subset A, Prop_to_Set (to_Prop (U ⊆ V))) 
  /- I am not sure whether coercions from `Type` to `Prop` and `Prop` to 
    `Set` are a good idea. They may introduce circuitious coercions. -/     

@[hott]
instance inc_hom {A : Set} (B C : 𝒫 A) : has_coe ↥(B ⊆ C) ↥(B ⟶ C) :=
  ⟨λ inc, inc⟩

@[hott]
def power_set_unique_hom {A : Set} {B C : 𝒫 A} (f g : B ⟶ C) : f = g :=
  @is_prop.elim _ (is_prop_subset B C) f g

@[hott, instance]
def power_set_cat_struct {A : Set} : category_struct (𝒫 A) := 
  category_struct.mk subset_refl subset_trans

@[hott, instance]
def power_set_precat {A : Set} : precategory (𝒫 A) :=
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
def subset_precat_has_hom {A : Set.{u}} [hA : has_hom.{v} A] (B : Subset A) :
  has_hom ↥B :=
has_hom.mk (λ x y : ↥B, @has_hom.hom _ hA x y)  

@[hott, instance]
def subset_precat_cat_struct {A : Set.{u}} [hA : category_struct.{v} A] 
  (B : Subset A) : category_struct ↥B :=
category_struct.mk (λ b : ↥B, @category_struct.id _ hA ↑b)
  (λ (b c d : ↥B) (f : b ⟶ c) (g : c ⟶ d), 
        @category_struct.comp _ hA ↑b ↑c ↑d f g)

@[hott, instance]
def subset_precat_precat {A : Set.{u}} [hA : precategory.{v} A] 
  (B : Subset A) : precategory ↥B :=
precategory.mk (λ (b c : ↥B) (f : b ⟶ c), precategory.id_comp f) 
               (λ (b c : ↥B) (f : b ⟶ c), precategory.comp_id f) 
               (λ (b c d e: ↥B) (f : b ⟶ c) (g : c ⟶ d) (h : d ⟶ e), 
                  precategory.assoc f g h) 

/- The inclusion of two subsets of a set that is a precategory defines a functor between the 
   underlying sets. 

   We need two equalities easily shown by induction. -/ 
@[hott]
def tr_tr_cat_id {C : Type u} [precategory.{v} C] {c c' : C} (p : c = c') : 
  p ▸[λ d, c' ⟶ d] (p ▸[λ d, d ⟶ c] 𝟙 c) = 𝟙 c' :=
begin hinduction p, refl end   

@[hott]
def tr_tr_cat_comp {C : Type u} [precategory.{v} C] {c₁ c₁' c₂ c₂' c₃ c₃': C} (p : c₁ = c₁') 
  (q : c₂ = c₂') (r : c₃ = c₃') (f : c₁' ⟶ c₂') (g : c₂' ⟶ c₃') : 
  r ▸[λ d, c₁' ⟶ d] (p ▸[λ d, d ⟶ c₃] ((p⁻¹ ▸[λ d, d ⟶ c₂] (q⁻¹ ▸[λ d, c₁' ⟶ d] f)) ≫ 
                                         (q⁻¹ ▸[λ d, d ⟶ c₃] (r⁻¹ ▸[λ d, c₂' ⟶ d] g)))) = f ≫ g :=
begin hinduction p, hinduction q, hinduction r, refl end

@[hott]
def functor_subsets_precat {A : Set.{u}} [hA : precategory.{v} A] {B C : Subset A} 
  (inc : B ⊆ C) : ↥B ⥤ ↥C :=
begin 
  fapply functor.mk, 
  { intro b, exact ⟨b.1, inc b.1 b.2⟩ }, 
  { intros b b' f, exact f },
  { intro b, refl },
  { intros b₁ b₂ b₃ f g, refl }
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

@[hott, hsimp]
def Set_isotocareqv {A B : Set.{u}} : (A ≅ B) -> (A ≃ B) :=
    assume i,
  have eqv_iso : is_equiv i.hom, from 
    have r_inv : ∀ b : B, i.hom (i.inv b) = b, from 
      assume b, homotopy_of_eq i.r_inv b,
    have l_inv : ∀ a : A, i.inv (i.hom a) = a, from 
      assume a, homotopy_of_eq i.l_inv a,
    adjointify i.hom i.inv r_inv l_inv,
  equiv.mk i.hom eqv_iso 

@[hott, hsimp, reducible]
def Set_isotoid {A B : Set.{u}} : (A ≅ B) -> (A = B) :=
  assume i,
  car_eq_to_set_eq (ua (Set_isotocareqv i))

@[hott, hsimp]
def Set_idtoiso_hom_eq {A B : Set.{u}} (p : A = B) : 
  ∀ a : A, ((idtoiso p).hom : A -> B) a = p ▸ a :=
begin
  hinduction p, rwr idtoiso_refl_eq, hsimp, 
  intro a, refl  
end 

@[hott, hsimp]
def Set_isotoid_eq_hom {A B : Set.{u}} (i : A ≅ B) : 
  ∀ a : A.carrier, (Set_isotoid i) ▸[λ A : Set.{u}, A.carrier] a = i.hom a :=
assume a, 
calc (Set_isotoid i) ▸ a = ((ap (trunctype.carrier) (Set_isotoid i)) ▸[λ A : Type u, A] a) : 
           (tr_ap (λ A : Type u, A) (trunctype.carrier) _ a)⁻¹
     ... = ((set_eq_to_car_eq (Set_isotoid i)) ▸[λ A : Type u, A] a) : 
           rfl      
     ... = ((ua (Set_isotocareqv i)) ▸[λ A : Type u, A] a) : 
           by rwr rinv_set_eq_car_eq _
     ... = (equiv_of_eq (ua (Set_isotocareqv i))).to_fun a : cast_def _ _
     ... = i.hom a : cast_ua (Set_isotocareqv i) a

@[hott, hsimp]
def Set_isotoid_eq_refl {A : Set.{u}} : Set_isotoid (id_is_iso A) = refl A :=
  calc Set_isotoid (id_is_iso A) = car_eq_to_set_eq (ua (equiv.refl ↥A)) : rfl
       ... = car_eq_to_set_eq (idpath ↥A) : by rwr ua_refl
       ... = refl A : idp_car_to_idp_set  

@[hott]
def Set_id_iso_rinv {A B : Set.{u}} : ∀ i : A ≅ B, idtoiso (Set_isotoid i) = i :=
  assume i,
  have hom_eq : ∀ a : A, ((idtoiso (Set_isotoid i)).hom : A -> B) a = i.hom a, from 
    assume a, (Set_idtoiso_hom_eq (Set_isotoid i) a) ⬝ Set_isotoid_eq_hom i a,
  hom_eq_to_iso_eq (eq_of_homotopy hom_eq)

@[hott]
def Set_id_iso_linv {A B : Set.{u}} : ∀ p : A = B, Set_isotoid (idtoiso p) = p :=
begin
  intro p, hinduction p, 
  rwr idtoiso_refl_eq, exact Set_isotoid_eq_refl
end  

@[hott, instance]
def Set_category : category Set.{u} :=
  have ideqviso : ∀ A B : Set.{u}, is_equiv (@idtoiso _ _ A B), from assume A B,
    adjointify idtoiso Set_isotoid Set_id_iso_rinv Set_id_iso_linv,
  category.mk ideqviso  

/- Categories in the algebraic hierarchy are categories of structured sets. The structures can
   be charcaterized even more specifically: They are Ω-structures 
   made up of functions and relations on the sets (see [HoTT-Book], Sec.9.8). Such structures 
   allow the construction of subsheaves of sections, see [topology.category.Top_sheaves]. 
   
   First-order signatures prescribe the number and arity of functions and relations in an
   Ω-structure. -/
@[hott]
structure fo_signature :=
  ( ops : Set.{0} ) 
  ( rels : Set.{0} )
  ( ops_arity : Π (o : ops), Set.{0} )
  ( rels_arity : Π (r : rels), Set.{0} )

@[hott]  
structure Ω_structure_on (sign : fo_signature) (carrier : Set) :=
  ( ops : ∀ o : sign.ops, ((sign.ops_arity o) -> carrier) -> carrier )
  ( rels : ∀ r : sign.rels, ((sign.rels_arity r) -> carrier) -> trunctype.{0} -1 )

/- The following three lemmas should be produced automatically. -/
@[hott]
def Ω_str_eq {sign : fo_signature} {carrier : Set} 
  {Ω_str₁ Ω_str₂ : Ω_structure_on sign carrier} : 
  (Ω_str₁.ops = Ω_str₂.ops) -> (Ω_str₁.rels = Ω_str₂.rels) -> (Ω_str₁ = Ω_str₂) :=
begin
  intros p_ops p_rels, 
  hinduction Ω_str₁ with ops₁ rels₁, hinduction Ω_str₂ with ops₂ rels₂,
  exact ap011 Ω_structure_on.mk p_ops p_rels
end    

@[hott]
def Ω_str_eq_eta {sign : fo_signature} {carrier : Set} 
  {Ω_str₁ Ω_str₂ : Ω_structure_on sign carrier} (p : Ω_str₁ = Ω_str₂) :
  Ω_str_eq (ap Ω_structure_on.ops p) (ap Ω_structure_on.rels p) = p := 
begin
  hinduction p, hinduction Ω_str₁, reflexivity
end    

@[hott, instance]
def is_set_Ω_structure_on (sign : fo_signature) (carrier : Set) : 
  is_set (Ω_structure_on sign carrier) :=
begin
  fapply is_set.mk, intros Ω_str₁ Ω_str₂ p q, 
  rwr <- Ω_str_eq_eta p, rwr <- Ω_str_eq_eta q,
  apply ap011 Ω_str_eq,
  apply is_set.elim, apply is_set.elim
end    

@[hott]
structure is_Ω_structure_hom {sign : fo_signature} {A B : Set.{u}} 
  (Ω_A : Ω_structure_on sign A) (Ω_B : Ω_structure_on sign B) (h : A -> B) :=
( ops_pres : ∀ (o : sign.ops) (x : (sign.ops_arity o) -> A), 
                                                     h (Ω_A.ops o x) = Ω_B.ops o (h ∘ x) ) 
( rels_pres : ∀ (r : sign.rels) (x : (sign.rels_arity r) -> A), 
                                                     Ω_A.rels r x -> Ω_B.rels r (h ∘ x) )                                                       

@[hott, instance]
def is_prop_is_Ω_Structure_hom {sign : fo_signature} {A B : Set.{u}} 
  (Ω_A : Ω_structure_on sign A) (Ω_B : Ω_structure_on sign B) (h : A -> B) : 
  is_prop (is_Ω_structure_hom Ω_A Ω_B h) :=
begin
  apply is_prop.mk, intros strh₁ strh₂, 
  hinduction strh₁ with ops_pres₁ rels_pres₁, hinduction strh₂ with ops_pres₂ rels_pres₂,
  fapply ap011 is_Ω_structure_hom.mk,
  { exact is_prop.elim _ _ },
  { exact is_prop.elim _ _ }
end    

@[hott]
def std_str_of_Ω_str (sign : fo_signature) : std_structure_on Set :=
begin
  fapply std_structure_on.mk,
  { exact λ S : Set, Ω_structure_on sign S },
  { intros S T Ω_Str_S Ω_Str_T h, 
    exact prop_resize (to_Prop (@is_Ω_structure_hom sign _ _ Ω_Str_S Ω_Str_T h)) },
  { intros A Ω_str_A, apply prop_to_prop_resize, fapply is_Ω_structure_hom.mk, 
    { intros o x, refl },
    { intros r x a, exact a } },
  { intros A B C Ω_str_A Ω_str_B Ω_str_C f g p_Ω_hom_f p_Ω_hom_g, 
    apply prop_to_prop_resize, fapply is_Ω_structure_hom.mk, 
    { intros o x, change g (f (Ω_str_A.ops o x)) = Ω_str_C.ops o ((f ≫ g) ∘ x), 
      rwr (prop_resize_to_prop p_Ω_hom_f).ops_pres o x,
      rwr (prop_resize_to_prop p_Ω_hom_g).ops_pres o (f ∘ x) },
    { intros r x a, change ↥(Ω_str_C.rels r (g ∘ (f ∘ x))), 
      apply (prop_resize_to_prop p_Ω_hom_g).rels_pres r (f ∘ x), 
      apply (prop_resize_to_prop p_Ω_hom_f).rels_pres r x, exact a } },
  { intros A Ω_str_A₁ Ω_str_A₂, fapply equiv.mk, 
    { intro Ω_str_homs, 
      hinduction Ω_str_A₁ with ops₁ rels₁, hinduction Ω_str_A₂ with ops₂ rels₂, 
      fapply ap011 Ω_structure_on.mk, 
      { apply eq_of_homotopy, intro o, apply eq_of_homotopy, intro x, 
        exact (prop_resize_to_prop Ω_str_homs.1).ops_pres o x },
      { apply eq_of_homotopy, intro r, apply eq_of_homotopy, intro x, 
        apply prop_iff_eq, 
        { intro rx₁, apply (prop_resize_to_prop Ω_str_homs.1).rels_pres r x, exact rx₁ },
        { intro rx₂, apply (prop_resize_to_prop Ω_str_homs.2).rels_pres r x, exact rx₂ } } },
    { fapply adjointify, 
      { intro Ω_str_eq, rwr Ω_str_eq, 
        have Ω_str_id : is_Ω_structure_hom Ω_str_A₂ Ω_str_A₂ (𝟙 A), from 
        begin 
          apply is_Ω_structure_hom.mk, 
          { intros o x, refl },
          { intros r x rx, exact rx }
        end,
        exact ⟨prop_to_prop_resize Ω_str_id, prop_to_prop_resize Ω_str_id⟩ },
      { intro b, exact @is_set.elim _ _ Ω_str_A₁ Ω_str_A₂ _ b },
      { intro a, exact is_prop.elim _ _ } } }
end  

@[hott]
def Ω_structure (sign : fo_signature) :=
  std_structure (std_str_of_Ω_str sign)

@[hott, instance]
def Ω_sign_str_precategory (sign : fo_signature) : 
  precategory (Ω_structure sign) := 
std_str_precategory (std_str_of_Ω_str sign)

@[hott, instance]
def Ω_str_precategory (sign : fo_signature) : 
  precategory (Ω_structure sign) := 
std_str_precategory (std_str_of_Ω_str sign)

@[hott, instance]
def Ω_sign_str_category (sign : fo_signature) : 
  category (Ω_structure sign) := 
structure_identity_principle (std_str_of_Ω_str sign)

/- The category of Ω-structures on sets having a given signature is usually too large to
   capture algebraic structures: These require that particular relations involving the
   operations are true for all possible arguments. 
   
   By prescribing logical equivalences of the signature relations to such relations and
   and requesting that they are always true we can define a predicate on the objects 
   of the Ω-structure category that gives a full subcategory. -/
@[hott]
def signature_laws (sign : fo_signature) :=
  Π (S : Ω_structure sign) (r : sign.rels) (args : (sign.rels_arity r) -> S.carrier), 
  trunctype.{0} -1

@[hott]
def Ω_structure_laws_pred {sign : fo_signature} (P : signature_laws sign) : 
  Ω_structure sign -> trunctype.{0} -1 :=
begin  
intro S, 
exact prop_resize 
      (to_Prop (∀ r args, (S.str.rels r args).carrier <-> (P S r args)) and
       to_Prop (∀ r args, is_true (P S r args)))
end                        

@[hott]
def Ω_str_subtype {sign : fo_signature} (P : signature_laws sign) := 
  sigma.subtype (λ S : Ω_structure sign, Ω_structure_laws_pred P S)

@[hott, instance]
def Ω_str_subtype_category {sign : fo_signature} (P : signature_laws sign) : 
  category (Ω_str_subtype P) :=
full_subcat_on_subtype (Ω_structure_laws_pred P)  

/- Subsets of the underlying sets of an object in a category of first-order signature 
   category inherit the structure of the object if the operations are closed on the 
   subset. -/
@[hott]
def ops_closed {sign : fo_signature} {S : Ω_structure sign} (R : Subset S.carrier) :=
  ∀ (o : sign.ops) (args : (sign.ops_arity o) -> S.carrier), 
    (∀ i : sign.ops_arity o, args i ∈ R) -> S.str.ops o args ∈ R 

@[hott]
def str_subobject {sign : fo_signature} {S : Ω_structure sign} {R : Subset S.carrier}
  (oc : ops_closed R) : Ω_structure sign :=
begin
  fapply std_structure.mk,
  { exact pred_Set R },
  { fapply Ω_structure_on.mk, 
    { intros o x, exact ⟨S.str.ops o (sigma.fst ∘ x), oc o (sigma.fst ∘ x) (λ i, (x i).2)⟩ },
    { intros r x, exact S.str.rels r (sigma.fst ∘ x) } }
end    

/- `str_subobject` is not the only structure on a subset `R` that is closed under the 
   Ω-operations on a set `S` and is compatible with the subset embedding: There may be 
   relations on elements in `R` in the Ω-structure on `S` that do not hold in the 
   Ω-structure on `R`. But `str_subobject` is terminal among all those structures. -/
@[hott]
def str_subobject_comp {sign : fo_signature} {S : Ω_structure sign} 
  {R : Subset S.carrier} (oc : ops_closed R) : 
  (std_str_of_Ω_str sign).H (str_subobject oc).str S.str (pred_Set_map R) :=
begin
  apply prop_to_prop_resize, apply is_Ω_structure_hom.mk,
  { intros o x, refl },
  { intros r x rx, exact rx }
end    

@[hott]
def terminal_str_on_subobj {sign : fo_signature} {S : Ω_structure sign} 
  {R : Subset S.carrier} (oc : ops_closed R) : 
  ∀ R_str : Ω_structure_on sign (pred_Set R), 
    (std_str_of_Ω_str sign).H R_str S.str (pred_Set_map R) ->
    (std_str_of_Ω_str sign).H R_str (str_subobject oc).str (𝟙 (pred_Set R)) :=
begin
 let substr := (str_subobject oc).str, 
 intros R_str R_str_comp, apply prop_to_prop_resize, apply is_Ω_structure_hom.mk, 
 { intros o x, change R_str.ops o x = substr.ops o x, apply pred_Set_map_is_inj, 
   rwr (prop_resize_to_prop R_str_comp).ops_pres o x },
 { intros r x rx, change ↥(substr.rels r x), 
   exact (prop_resize_to_prop R_str_comp).rels_pres r x rx }
end                              

/- The induced structure on a subset of structured sets that is closed under the 
   structure operation does not necessarily satisfy the laws of a predicate if the 
   laws are satisfied by the structured set.
   
   But this is the case if the laws are functorial and left-exact. -/
@[hott]
def funct_sign_laws {sign : fo_signature} (P : signature_laws sign) :=
  Π {S R : Ω_structure sign} (f : R.carrier -> S.carrier) (r : sign.rels) 
  (args : (sign.rels_arity r) -> R.carrier), P R r args -> P S r (f ∘ args)   

@[hott]
def left_exact_sign_laws {sign : fo_signature} (P : signature_laws sign) :=
  Π {S R : Ω_structure sign} (f : R.carrier -> S.carrier) (r : sign.rels) 
    (args : (sign.rels_arity r) -> R.carrier), 
  is_set_injective f -> (P S r (f ∘ args) -> P R r args)  

@[hott]
def law_str_subset {sign : fo_signature} {P : signature_laws sign} {S : Ω_str_subtype P}
  (funct : funct_sign_laws P) (le_laws : left_exact_sign_laws P) (R : Subset S.1.carrier) 
  (oc : ops_closed R) : Ω_str_subtype P :=
begin
  let emb_map : (str_subobject oc).carrier -> S.1.carrier := pred_Set_map R,
  fapply sigma.mk,
  { exact str_subobject oc },
  { change ↥(Ω_structure_laws_pred P (str_subobject oc)),
    apply prop_to_prop_resize, apply prod.mk, 
    { intros r args, apply prod.mk, 
      { intro so_rel, apply le_laws emb_map r args (pred_Set_map_is_inj R),
        apply ((prop_resize_to_prop S.2).1 r (((pred_Set_map R)) ∘ args)).1, 
        assumption },
      { intro so_P, apply ((prop_resize_to_prop S.2).1 r (((pred_Set_map R)) ∘ args)).2, 
        apply funct emb_map r args, assumption } },
    { intros r args, apply prod.mk, 
      { intro so_P, exact true.intro },
      { intro t, apply le_laws emb_map r args (pred_Set_map_is_inj R),
        apply ((prop_resize_to_prop S.2).2 r (((pred_Set_map R)) ∘ args)).2,
        assumption } } }
end

end categories

end hott