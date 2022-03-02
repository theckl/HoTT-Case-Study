import sets.algebra init2 sets.axioms sets.theories categories.basic

universes v v' u u' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc hott.is_equiv hott.equiv hott.categories 

namespace categories

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

/- The type of functors between two precategories has a precategory 
   structure: The morphisms are the natural transformations, and the type of natural 
   transformations between two given functors is a set. -/
@[hott]
def nat_trans_eq [precategory.{v} C] [precategory.{v'} D] {F G : C ⥤ D} {φ ψ : F ⟹ G} :
  (φ.app = ψ.app) -> φ = ψ :=
begin 
  intros, hinduction φ, hinduction ψ, apply apd011 nat_trans.mk a, 
  apply pathover_of_tr_eq, apply eq_of_homotopy3, intros c₁ c₂ f, exact is_prop.elim _ _ 
end

@[hott]
def nat_trans_eq_idp [precategory.{v} C] [precategory.{v'} D] {F G : C ⥤ D} (φ : F ⟹ G) :
  @nat_trans_eq _ _ _ _ _ _ φ φ idp = idp :=
begin 
  hinduction φ, hsimp, 
  change apd011 nat_trans.mk idp (pathover_idp_of_eq _ _) = _, hsimp,
  have H : (λ (c₁ c₂ : C) (f : c₁ ⟶ c₂), is_prop.elim (naturality f) (naturality f)) =
           λ (c₁ c₂ : C) (f : ↥(c₁ ⟶ c₂)), idp, from 
  begin apply eq_of_homotopy3, intros c₁ c₂ f,  exact is_prop_elim_self _ end, 
  rwr H, rwr eq_of_homotopy3_id 
end

@[hott]
def nat_trans_eq_eta [precategory.{v} C] [precategory.{v'} D] {F G : C ⥤ D} {φ ψ : F ⟹ G}
  (p : φ = ψ) : nat_trans_eq (ap nat_trans.app p) = p :=
begin hinduction p, hinduction φ, rwr ap_idp, rwr nat_trans_eq_idp _ end  

@[hott, instance]
def nat_trans_is_set [precategory.{v} C] [precategory.{v'} D] :
  Π F G : C ⥤ D, is_set (F ⟹ G) :=
begin 
  intros F G, apply is_set.mk, intros s t p q,  
  rwr <- nat_trans_eq_eta p, rwr <- nat_trans_eq_eta q, 
  apply ap nat_trans_eq, exact is_set.elim _ _
end  

@[hott, instance]
def functor_has_hom [precategory.{v} C] [precategory.{v'} D] : has_hom (C ⥤ D) :=
  has_hom.mk (λ F G : C ⥤ D, to_Set (F ⟹ G))   

@[hott, instance]
def functor_cat_struct [precategory.{v} C] [precategory.{v'} D] : 
  category_struct (C ⥤ D) :=
begin 
  fapply category_struct.mk,
  { intro F, fapply nat_trans.mk, 
    { intro c, exact 𝟙 (F.obj c) },
    { intros c c' f, hsimp } },
  { intros F G H s t, fapply nat_trans.mk, 
    { intro c, exact s.app c ≫ t.app c },
    { intros c c' f, rwr <- precategory.assoc (F.map f) _ _, 
      rwr nat_trans.naturality, rwr precategory.assoc (s.app c) _ _, 
      rwr nat_trans.naturality, rwr precategory.assoc (s.app c) } } 
end  

@[hott, instance]
def functor_precategory [precategory.{v} C] [precategory.{v'} D] :
  precategory (C ⥤ D) :=
begin
  fapply precategory.mk,
  { intros F G s, apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change 𝟙 (F.obj c) ≫ s.app c = _, rwr precategory.id_comp },
  { intros F G s, apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change s.app c ≫ 𝟙 (G.obj c) = _, rwr precategory.comp_id },
  { intros E F G H s t u, apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change (s.app c ≫ t.app c) ≫ u.app c = s.app c ≫ t.app c ≫ u.app c, 
    rwr precategory.assoc }
end  

/- If the target of the functors is a category, the precategory of functors is a category. -/
@[hott]
def functor_iso_to_isos [precategory.{v} C] [precategory.{v'} D] {F G : C ⥤ D} :
  (F ≅ G) -> Π c : C, F.obj c ≅ G.obj c :=
begin 
  intros i c, fapply iso.mk,
  { exact i.hom.app c },
  { exact i.inv.app c },
  { change (i.inv ≫ i.hom).app c = _, rwr i.r_inv },
  { change (i.hom ≫ i.inv).app c = _, rwr i.l_inv }
end     

@[hott] 
def functor_isoid_to_isoids [precategory.{v} C] [precategory.{v'} D] {F : C ⥤ D} :
  Π (c : C), functor_iso_to_isos (id_is_iso F) c = id_is_iso (F.obj c) :=
begin intro c, apply hom_eq_to_iso_eq, refl end  

@[hott]
def functor_idtoiso_comp [precategory.{v} C] [precategory.{v'} D] {F G : C ⥤ D} 
  (p : F = G) (c : C) : 
  nat_trans.app (idtoiso p).hom c = (idtoiso (apd10 (ap functor.obj p) c)).hom :=
begin hinduction p, rwr idtoiso_refl_eq end  

@[hott]
def functor_isotoid [precategory.{v} C] [category.{v'} D] {F G : C ⥤ D} :
  (F ≅ G) -> F = G :=
begin
  have Q : Π (H₂ : C -> D) (p : F.obj = H₂) (c₁ c₂ : C) (h : c₁ ⟶ c₂), 
            (p ▸[λ H : C -> D, Π (c₁ c₂ : C) (h : c₁ ⟶ c₂), H c₁ ⟶ H c₂] F.map) c₁ c₂ h = 
               (idtoiso (apd10 p c₁)).inv ≫ F.map h ≫ (idtoiso (apd10 p c₂)).hom, from 
    begin intros H₂ p c₁ c₂ h, hinduction p, hsimp end,
  intro i, fapply functor_eq, 
  { apply eq_of_homotopy, intro c, exact category.isotoid (functor_iso_to_isos i c) },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros c₁ c₂ h, rwr Q, 
    rwr homotopy_eq_rinv, 
    change (idtoiso (idtoiso⁻¹ᶠ (functor_iso_to_isos i c₁)))⁻¹ʰ ≫ _ ≫
           (idtoiso (idtoiso⁻¹ᶠ (functor_iso_to_isos i c₂))).hom = _, 
    rwr category.idtoiso_rinv, rwr category.idtoiso_rinv, apply eq.inverse, 
    apply iso_move_lr, change i.hom.app c₁ ≫ _ = _ ≫ i.hom.app c₂, rwr i.hom.naturality }
end     

@[hott, instance]
def functor_category [precategory.{v} C] [category.{v'} D] : category (C ⥤ D) :=
begin
  apply category.mk, intros F G, fapply adjointify, 
  { exact functor_isotoid },
  { intro i, apply hom_eq_to_iso_eq, apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    rwr functor_idtoiso_comp, 
    change (idtoiso (@apd10 _ _ F.obj G.obj (ap functor.obj (functor_eq _ _ _ _)) c)).hom = _,
    rwr functor_eq_obj, rwr homotopy_eq_rinv,
    change (idtoiso (idtoiso⁻¹ᶠ (functor_iso_to_isos i c))).hom = _, 
    rwr category.idtoiso_rinv },
  { intro p, hinduction p, rwr idtoiso_refl_eq, change functor_eq C D _ _ = idp, 
    rwr <- functor_eq_idp, fapply apd011 (functor_eq C D), 
    { change eq_of_homotopy (λ (c : C), category.isotoid 
                               (@functor_iso_to_isos C _ _ _ _ _  (id_is_iso F) c)) = idpath _,
      rwr <- eq_of_homotopy_idp, apply ap eq_of_homotopy, apply eq_of_homotopy, intro c, 
      change category.isotoid (functor_iso_to_isos (id_is_iso F) c) = idpath (F.obj c),
      rwr functor_isoid_to_isoids, rwr isotoid_id_refl },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
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


/- `Set.{u}` is a category - the category of `Type u`-small sets. -/
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


/- The subobjects of an object, together with their monomorphism-preserving homomorphisms
   defined in [categories.basic], form a category. -/  
@[hott, instance]
def subobject_has_hom {C : Type u} [category.{v} C] {c : C} : has_hom (subobject c) :=
  has_hom.mk (λ a b : subobject c, Set.mk (subobject_hom a b) (is_trunc_succ _ -1))

@[hott]
def id_subobject {C : Type u} [category.{v} C] {c : C} (a : subobject c) : subobject_hom a a :=
  begin fapply hom_of_monos.mk a.is_mono a.is_mono, exact 𝟙 a.obj, hsimp end  

@[hott] 
def comp_subobject {C : Type u} [category.{v} C] {c : C} (a₁ a₂ a₃ : subobject c) :
  subobject_hom a₁ a₂ -> subobject_hom a₂ a₃ -> subobject_hom a₁ a₃ :=
begin 
  intros f g, fapply hom_of_monos.mk a₁.is_mono a₃.is_mono, exact f.hom_obj ≫ g.hom_obj, 
  rwr precategory.assoc, rwr g.fac, rwr f.fac 
end  

@[hott, instance]
def subobject_cat_struct {C : Type u} [category.{v} C] {c : C} : 
  category_struct (subobject c) :=
category_struct.mk id_subobject comp_subobject

@[hott, instance]
def subobject_precategory {C : Type u} [category.{v} C] {c : C} : 
  precategory (subobject c) :=
have ic : Π (a b : subobject c) (f : a ⟶ b), 𝟙 a ≫ f = f, from 
  assume a b f, by exact is_prop.elim _ _,
have ci : Π (a b : subobject c) (f : a ⟶ b), f ≫ 𝟙 b = f, from 
  assume a b f, by exact is_prop.elim _ _,
have as : Π (a₁ a₂ a₃ a₄ : subobject c) (f : a₁ ⟶ a₂) (g : a₂ ⟶ a₃) (h : a₃ ⟶ a₄),
             (f ≫ g) ≫ h = f ≫ (g ≫ h), from 
  assume a₁ a₂ a₃ a₄ f g h, by exact is_prop.elim _ _,
precategory.mk ic ci as  

@[hott]
def iso_of_monos_to_iso {C : Type u} [category.{v} C] {c : C} (a b : subobject c) :
  (iso_of_monos a.is_mono b.is_mono) -> (a ≅ b) :=
begin 
  intro im, fapply iso.mk, 
  { fapply hom_of_monos.mk, exact im.iso_obj.hom, exact im.fac }, 
  { fapply hom_of_monos.mk, exact im.iso_obj.inv, apply eq.inverse, apply iso_move_lr, 
    exact im.fac },
  exact is_prop.elim _ _, exact is_prop.elim _ _ 
end

@[hott]
def iso_to_iso_of_monos {C : Type u} [category.{v} C] {c : C} (a b : subobject c) :
  (a ≅ b) -> (iso_of_monos a.is_mono b.is_mono) :=
begin 
  intro i, fapply iso_of_monos.mk, 
  { fapply iso.mk, exact i.hom.hom_obj, exact i.inv.hom_obj, 
    exact ap hom_of_monos.hom_obj i.r_inv, exact ap hom_of_monos.hom_obj i.l_inv },
  { exact i.hom.fac }
end    

@[hott]
def iso_of_monos_eqv_iso {C : Type u} [category.{v} C] {c : C} (a b : subobject c) :
  (iso_of_monos a.is_mono b.is_mono) ≃ (a ≅ b) :=
begin 
  fapply equiv.mk,
  { exact iso_of_monos_to_iso a b },
  { fapply adjointify, 
    { exact iso_to_iso_of_monos a b },
    { intro i, apply hom_eq_to_iso_eq, exact is_prop.elim _ _ },
    { intro i, exact is_prop.elim _ _ } }
end  

@[hott]
def subobj_idtoiso {C : Type u} [category.{v} C] {c : C} (a b : subobject c) : 
  @idtoiso _ _ a b = (iso_of_monos_eqv_iso a b).to_fun ∘ 
                     (equal_subobj_eqv_iso_mono a b).to_fun :=
begin apply eq_of_homotopy, intro p, apply hom_eq_to_iso_eq, exact is_prop.elim _ _ end                       

@[hott, instance]
def subobject_category {C : Type u} [category.{v} C] {c : C} : 
  category (subobject c) :=
begin apply category.mk, intros a b, rwr subobj_idtoiso a b, apply_instance end    

end categories

end hott