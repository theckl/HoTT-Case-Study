import sets.algebra categories.basic

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.set hott.subset hott.is_trunc hott.precategories

namespace categories

/- To construct the opposite category, we use the mathlib-trick in [data.opposite]
   that allows the elaborator to do most of the work. -/    
@[hott]
def opposite {C : Type u}: Type u := C 

notation C `ᵒᵖ`:std.prec.max_plus := @opposite C

@[hott]
def op_Set (C : Set.{u}) : Set :=
  Set.mk Cᵒᵖ (C.struct)

namespace opposite

section
variables {C : Type u} {D : Type u'} {E : Type u''} {F : Type u'''}

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

end

end opposite

open opposite

section
variables {C : Type u} {D : Type u'} {E : Type u''} {F : Type u'''}

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
def category_struct.opposite [is_precat.{v} C] : category_struct.{v} Cᵒᵖ :=
  category_struct.mk (λ x, hom_op (𝟙 (unop x))) 
                     (λ _ _ _ f g, hom_op (hom_unop g ≫ hom_unop f))

@[hott]
def id_comp_op [is_precat.{v} C] : ∀ (x y : Cᵒᵖ) (f : x ⟶ y), 𝟙 x ≫ f = f := 
begin intros x y f, hsimp end
   
@[hott]
def comp_id_op [is_precat.{v} C] : ∀ (x y : Cᵒᵖ) (f : x ⟶ y), f ≫ 𝟙 y = f := 
begin intros x y f, hsimp end

@[hott]
def assoc_op [is_precat.{v} C] : ∀ (x y z w : Cᵒᵖ) (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ w), 
  (f ≫ g) ≫ h = f ≫ g ≫ h := 
begin 
  intros x y z w f g h, 
  change hom_op (hom_unop h ≫ hom_unop (hom_op (hom_unop g ≫ hom_unop f))) = 
         hom_op (hom_unop (hom_op (hom_unop h ≫ hom_unop g)) ≫ hom_unop f),
  hsimp       
end  

@[hott, instance]
def is_precat.opposite [is_precat.{v} C] : is_precat.{v} Cᵒᵖ :=
  is_precat.mk id_comp_op comp_id_op assoc_op                   

@[hott]
def hom_op_funct [is_precat.{v} C] {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
  hom_op (f ≫ g) = hom_op g ≫ hom_op f := rfl

/- The opposite category. 
   We show the equivalence by splitting it up in three steps and using that maps from 
   `a = b` are determined by `rfl` if `a` and `b` are allowed to vary freely. -/
@[hott, hsimp]
def id_op_to_id [is_precat.{v} C] : Π {a b : Cᵒᵖ}, (a = b) -> (unop a = unop b) :=
  begin intros a b p, hinduction p, exact rfl end  

@[hott, hsimp]
def id_to_id_op [is_precat.{v} C] : Π {a b : Cᵒᵖ}, (unop a = unop b) -> (a = b) :=
  assume a b p_op, 
  calc a   = op (unop a) : by hsimp
       ... = op (unop b) : ap op p_op 
       ... = b : op_unop b 

@[hott, instance]
def id_op_eqv_id [is_precat.{v} C] : ∀ a b : Cᵒᵖ, is_equiv (@id_op_to_id _ _ a b) :=
  assume a b,
  have rinv : ∀ p_op : unop a = unop b, id_op_to_id (id_to_id_op p_op) = p_op, from  
    begin intro p_op, hsimp, rwr ap_compose', hsimp end, 
  have linv : ∀ p : a = b, id_to_id_op (id_op_to_id p) = p, from 
    begin intro p, hsimp, rwr ap_compose', hsimp end,
  is_equiv.adjointify id_op_to_id id_to_id_op rinv linv   

@[hott, hsimp]
def iso_to_iso_op [is_precat.{v} C] : ∀ {a b : Cᵒᵖ}, (unop a ≅ unop b) -> (a ≅ b) :=
begin 
  intros a b i,
  fapply iso.mk, 
    rwr <- op_unop a, rwr <- op_unop b, exact hom_op i.ih.inv,
    fapply is_iso.mk,
    rwr <- op_unop a, rwr <- op_unop b, exact hom_op i.hom,
    change hom_op (i.ih.inv ≫ i.hom) = hom_op (𝟙 (unop b)), 
    apply ap hom_op, exact i.ih.r_inv,
    change hom_op (i.hom ≫ i.ih.inv) = hom_op (𝟙 (unop a)), 
    apply ap hom_op, exact i.ih.l_inv   
end

@[hott, hsimp]
def iso_op_to_iso [is_precat.{v} C] : ∀ {a b : Cᵒᵖ}, (a ≅ b) -> (unop a ≅ unop b) :=
begin
  intros a b i,
  fapply iso.mk,
    exact hom_unop i.ih.inv, fapply is_iso.mk,
    exact hom_unop i.hom,
  { rwr <- @hom_unop_op _ _ _ _ (hom_unop i.hom ≫ hom_unop i.ih.inv),  
    rwr <- @hom_unop_op _ _ _ _ (𝟙 (unop b)), exact ap hom_unop (i.ih.r_inv) },
  { rwr <- @hom_unop_op _ _ _ _ (hom_unop i.ih.inv ≫ hom_unop i.hom),  
    rwr <- @hom_unop_op _ _ _ _ (𝟙 (unop a)), exact ap hom_unop (i.ih.l_inv) }
end  

@[hott, instance]
def iso_eqv_iso_op [is_precat.{v} C] : ∀ a b : Cᵒᵖ, is_equiv (@iso_to_iso_op _ _ a b) :=
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
def idtoiso_rfl_eq [is_cat.{v} C] : ∀ a : Cᵒᵖ, 
  iso_to_iso_op (idtoiso (id_op_to_id (@rfl _ a))) = 
  idtoiso (@rfl _ a) :=
begin intro a, apply hom_eq_to_iso_eq, change 𝟙 a = 𝟙 a, refl end 

@[hott, instance]
def ideqviso_op [is_cat.{v} C] : ∀ a b : Cᵒᵖ, is_equiv (@idtoiso _ _ a b) :=
  assume a b,
  let f := @id_op_to_id _ _ a b, g := @idtoiso _ _ (unop a) (unop b), 
      h := @iso_to_iso_op _ _ a b in
  have id_optoiso_op : is_equiv (h ∘ g ∘ f), from is_equiv.is_equiv_compose h (g ∘ f), 
  let hgf := λ (a b : Cᵒᵖ) (p : a = b), 
             iso_to_iso_op (idtoiso (id_op_to_id p)) in
  have idtoiso_eq : hgf a b = @idtoiso _ _ a b, from fn_id_rfl _ _ idtoiso_rfl_eq a b,
  begin rwr <- idtoiso_eq; exact id_optoiso_op end

@[hott, instance]
def category.opposite [is_cat.{v} C] : is_cat.{v} Cᵒᵖ :=
  is_cat.mk ideqviso_op 

@[hott]
def opposite_functor [is_precat.{v} C] [is_precat.{v'} D] : (C ⥤ D) -> (Cᵒᵖ ⥤ Dᵒᵖ) :=
begin
  intro F, fapply precategories.functor.mk,
  { intro c, exact op (F.obj (unop c)) },
  { intros x y f, apply hom_op, exact F.map (hom_unop f) },
  { intro x, hsimp, refl },
  { intros x y z f g, hsimp, refl }
end


/- The type of functors between two precategories has a precategory 
   structure: The morphisms are the natural transformations, and the type of natural 
   transformations between two given functors is a set. -/
@[hott]
def nat_trans_eq [is_precat.{v} C] [is_precat.{v'} D] 
  {F G : C ⥤ D} {φ ψ : F ⟹ G} : (φ.app = ψ.app) -> φ = ψ :=
begin 
  intros, hinduction φ, hinduction ψ, apply apd011 nat_trans.mk a, 
  apply pathover_of_tr_eq, apply eq_of_homotopy3, intros c₁ c₂ f, exact is_prop.elim _ _ 
end

@[hott]
def nat_trans_eq_idp [is_precat.{v} C] [is_precat.{v'} D] {F G : C ⥤ D} (φ : F ⟹ G) :
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
def nat_trans_eq_eta [is_precat.{v} C] [is_precat.{v'} D] {F G : C ⥤ D} {φ ψ : F ⟹ G}
  (p : φ = ψ) : nat_trans_eq (ap nat_trans.app p) = p :=
begin hinduction p, hinduction φ, rwr ap_idp, rwr nat_trans_eq_idp _ end  

@[hott, instance]
def nat_trans_is_set [is_precat.{v} C] [is_precat.{v'} D] :
  Π F G : C ⥤ D, is_set (F ⟹ G) :=
begin 
  intros F G, apply is_set.mk, intros s t p q,  
  rwr <- nat_trans_eq_eta p, rwr <- nat_trans_eq_eta q, 
  apply ap nat_trans_eq, exact is_set.elim _ _
end  

@[hott, instance]
def functor_has_hom [is_precat.{v} C] [is_precat.{v'} D] : has_hom (C ⥤ D) :=
  has_hom.mk (λ F G : C ⥤ D, to_Set (F ⟹ G))   

@[hott, reducible]
def nat_trans_id [is_precat.{v} C] [is_precat.{v'} D] (F : C ⥤ D) : F ⟹ F :=
  nat_trans.mk (λ c : C, 𝟙 (F.obj c)) (λ (c c' : C) (f : c ⟶ c'), by hsimp) 

@[hott, reducible]
def nat_trans_comp [is_precat.{v} C] [is_precat.{v'} D] (F G H : C ⥤ D) 
  (α : F ⟹ G) (β : G ⟹ H) : F ⟹ H :=
nat_trans.mk (λ c, α.app c ≫ β.app c) 
             (λ (c c' : C) (f : c ⟶ c'), by rwr <- is_precat.assoc (F.map f) _ _; 
                      rwr nat_trans.naturality; rwr is_precat.assoc (α.app c) _ _; 
                      rwr nat_trans.naturality; rwr is_precat.assoc (α.app c))  

@[hott, instance]
def functor_cat_struct [is_precat.{v} C] [is_precat.{v'} D] : 
  category_struct (C ⥤ D) :=
category_struct.mk (λ F, nat_trans_id F) (λ F G H α β, nat_trans_comp F G H α β)

@[hott, instance]
def functor_is_precat [is_precat.{v} C] [is_precat.{v'} D] :
  is_precat (C ⥤ D) :=
begin
  fapply is_precat.mk,
  { intros F G s, apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change 𝟙 (F.obj c) ≫ s.app c = _, rwr is_precat.id_comp },
  { intros F G s, apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change s.app c ≫ 𝟙 (G.obj c) = _, rwr is_precat.comp_id },
  { intros E F G H s t u, apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change (s.app c ≫ t.app c) ≫ u.app c = s.app c ≫ t.app c ≫ u.app c, 
    rwr is_precat.assoc }
end  

/- If the target of the functors is a category, the precategory of functors is a category. -/
@[hott]
def functor_iso_to_isos [is_precat.{v} C] [is_precat.{v'} D] 
  {F G : C ⥤ D} : (F ≅ G) -> Π c : C, F.obj c ≅ G.obj c :=
begin 
  intros i c, fapply iso.mk,
  { exact i.hom.app c }, fapply is_iso.mk,
  { exact i.ih.inv.app c },
  { change (i.ih.inv ≫ i.hom).app c = _, rwr i.ih.r_inv },
  { change (i.hom ≫ i.ih.inv).app c = _, rwr i.ih.l_inv }
end     

@[hott] 
def functor_isoid_to_isoids [is_precat.{v} C] [is_precat.{v'} D]
 {F : C ⥤ D} : Π (c : C), functor_iso_to_isos (id_iso F) c =
                           id_iso (F.obj c) :=
begin intro c, apply hom_eq_to_iso_eq, refl end  

@[hott]
def functor_idtoiso_comp [is_precat.{v} C] [is_precat.{v'} D] {F G : C ⥤ D} 
  (p : F = G) (c : C) : 
  nat_trans.app (idtoiso p).hom c = (idtoiso (apd10 (ap functor.obj p) c)).hom :=
begin hinduction p, rwr idtoiso_refl_eq end  

@[hott]
def functor_isotoid [is_precat.{v} C] [HD : is_cat.{v'} D] {F G : C ⥤ D} :
  (F ≅ G) -> F = G :=
begin
  intro i, fapply functor_eq', 
  { intro c, 
    exact @category.isotoid D HD _ _ (@functor_iso_to_isos _ _ _ _ F G i c) },
  { intros c₁ c₂ h, rwr id_inv_iso_inv, 
    change (idtoiso (idtoiso⁻¹ᶠ (functor_iso_to_isos i c₁))).ih.inv ≫ _ ≫
           (idtoiso (idtoiso⁻¹ᶠ (functor_iso_to_isos i c₂))).hom = _, 
    rwr @category.idtoiso_rinv (Category.mk D HD), 
    rwr @category.idtoiso_rinv (Category.mk D HD), apply eq.inverse, 
    apply iso_move_lr, change i.hom.app c₁ ≫ _ = _ ≫ i.hom.app c₂, rwr i.hom.naturality }
end     

@[hott, instance]
def functor_is_cat [is_precat.{v} C] [HD : is_cat.{v'} D] : is_cat (C ⥤ D) :=
begin
  apply is_cat.mk, intros F G, fapply is_equiv.adjointify, 
  { exact functor_isotoid },
  { intro i, apply hom_eq_to_iso_eq, apply nat_trans_eq, apply eq_of_homotopy, 
    intro c, rwr functor_idtoiso_comp, 
    change (idtoiso (@apd10 _ _ F.obj G.obj (ap functor.obj (functor_eq' _ _)) c)).hom = _,
    rwr functor_eq_obj', rwr homotopy_eq_rinv,
    change (idtoiso (idtoiso⁻¹ᶠ (functor_iso_to_isos i c))).hom = _, 
    rwr @category.idtoiso_rinv (Category.mk D HD) },
  { intro p, hinduction p, rwr idtoiso_refl_eq, 
    change functor_eq' _ _ = idp, 
    rwr <- functor_eq_idp, fapply apd011 (functor_eq), 
    { change eq_of_homotopy (λ (c : C), @category.isotoid D HD _ _ 
                               (@functor_iso_to_isos C _ _ _ _ _ (id_iso F) c)) = idpath _,
      rwr <- eq_of_homotopy_idp, apply ap eq_of_homotopy, apply eq_of_homotopy, intro c, 
      change @category.isotoid D HD _ _ (functor_iso_to_isos (id_iso F) c) = idpath (F.obj c),
      rwr functor_isoid_to_isoids, rwr isotoid_id_refl },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end

@[hott]
def functor_Category (C : Type _) [is_precat.{v} C] (D : Type _) 
  [is_cat.{v'} D] : Category := Category.mk (C ⥤ D) functor_is_cat

/- Whiskering of natural transformations with functors: [HoTT-Book, Def.9.2.7] -/
@[hott]
def tr_whisk_l [is_precat.{v} C] [is_precat.{v'} D] [is_precat.{v''} E]
  {F : D ⥤ E} {G : D ⥤ E} (H : C ⥤ D) (α : F ⟶ G) : H ⋙ F ⟶ H ⋙ G :=
begin
  fapply nat_trans.mk,
  { intro c, exact α.app (H.obj c) },
  { intros c c' f, 
    change F.map (H.map f) ≫ α.app (H.obj c') = α.app (H.obj c) ≫ G.map (H.map f),
    rwr α.naturality }
end  

@[hott]
def tr_whisk_l_id [is_precat.{v} C] [is_precat.{v'} D] [is_precat.{v''} E]
  (H : C ⥤ D) (F : D ⥤ E) : tr_whisk_l H (𝟙 F) = 𝟙 (H ⋙ F) :=
begin apply nat_trans_eq, apply eq_of_homotopy, intro c, exact idp end  

@[hott]
def tr_whisk_r [is_precat.{v} C] [is_precat.{v'} D] [is_precat.{v''} E]
  {F : C ⥤ D} {G : C ⥤ D} (α : F ⟶ G) (H : D ⥤ E) : F ⋙ H ⟶ G ⋙ H :=
begin
  fapply nat_trans.mk,
  { intro c, exact H.map (α.app c) },
  { intros c c' f, 
    change H.map (F.map f) ≫ H.map (α.app c') = H.map (α.app c) ≫ H.map (G.map f),
    rwr <- H.map_comp, rwr <- H.map_comp, rwr α.naturality }
end

@[hott]
def tr_whisk_r_id [is_precat.{v} C] [is_precat.{v'} D] [is_precat.{v''} E]
  (F : C ⥤ D) (H : D ⥤ E) : tr_whisk_r (𝟙 F) H = 𝟙 (F ⋙ H) :=
begin 
  apply nat_trans_eq, apply eq_of_homotopy, intro c, 
  change H.map (𝟙 (F.obj c)) = 𝟙 (H.obj (F.obj c)), 
  rwr functor.map_id 
end

/- Horizontal composition of natural transformations can be defined in two ways that 
   are (propositionally) equal [HoTT-Book, Lem.9.2.8]. -/
@[hott]
def horiz_comp_eq [is_precat.{v} C] [is_precat.{v'} D] [is_precat.{v''} E]
  {F : C ⥤ D} {G : C ⥤ D} {H : D ⥤ E} {K : D ⥤ E} (γ : F ⟶ G) (δ : H ⟶ K) :
  tr_whisk_r γ H ≫ tr_whisk_l G δ = tr_whisk_l F δ ≫ tr_whisk_r γ K :=
begin 
  apply nat_trans_eq, apply eq_of_homotopy, intro c, 
  change H.map (γ.app c) ≫ δ.app (G.obj c) = δ.app (F.obj c) ≫ K.map (γ.app c),
  rwr δ.naturality 
end      

end

/- The composition of functors has left and right neutral and is associative. 
   We construct these equalities from natural isomorphisms. -/
@[hott, reducible]
def l_neutral_funct_iso {C D : Type _} [is_precat C] [is_precat D] (F : C ⥤ D) :
  (id_functor C ⋙ F) ≅ F :=
begin 
  fapply iso.mk,
  { fapply nat_trans.mk, 
    { intro c, exact 𝟙 (F.obj c) },
    { intros c c' f, hsimp } }, fapply is_iso.mk,
  { fapply nat_trans.mk, 
    { intro c, exact 𝟙 (F.obj c) },
    { intros c c' f, hsimp } },
  { apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change (nat_trans.mk _ _).app c ≫ (nat_trans.mk _ _).app c = _, hsimp, exact idp },
  { apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change (nat_trans.mk _ _).app c ≫ (nat_trans.mk _ _).app c = _, hsimp, exact idp } 
end  

@[hott]
def l_neutral_funct {C D : Type _} [is_precat C] [is_cat D] (F : C ⥤ D) :
  (id_functor C ⋙ F) = F :=
have i : (id_functor C ⋙ F) ≅ F, from l_neutral_funct_iso F,
@category.isotoid (C ⥤ D) (functor_is_cat) (id_functor C ⋙ F) F i

@[hott, reducible]
def r_neutral_funct_iso {C D : Type _} [is_precat C] [is_precat D] 
  (F : C ⥤ D) : (F ⋙ id_functor D) ≅ F :=
begin 
  fapply iso.mk,
  { fapply nat_trans.mk, 
    { intro c, exact 𝟙 (F.obj c) },
    { intros c c' f, hsimp } }, fapply is_iso.mk,
  { fapply nat_trans.mk, 
    { intro c, exact 𝟙 (F.obj c) },
    { intros c c' f, hsimp } },
  { apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change (nat_trans.mk _ _).app c ≫ (nat_trans.mk _ _).app c = _, hsimp, exact idp },
  { apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change (nat_trans.mk _ _).app c ≫ (nat_trans.mk _ _).app c = _, hsimp, exact idp } 
end 

@[hott]
def r_neutral_funct {C D : Type _} [is_precat C] [is_cat D] 
  (F : C ⥤ D) : (F ⋙ id_functor D) = F :=
@category.isotoid (C ⥤ D) (functor_is_cat) _ _ (r_neutral_funct_iso F)

@[hott, reducible]
def assoc_funct_iso {C D E F : Type _} [is_precat C] [is_precat D] 
  [is_precat E] [is_precat F] (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) : 
  ((G ⋙ H) ⋙ I) ≅ (G ⋙ (H ⋙ I)) :=
begin
  fapply iso.mk,
  { fapply nat_trans.mk,
    { intro c, exact 𝟙 (I.obj (H.obj (G.obj c))) },
    { intros c c' f, hsimp } }, fapply is_iso.mk,
  { fapply nat_trans.mk,
    { intro c, exact 𝟙 (I.obj (H.obj (G.obj c))) },
    { intros c c' f, hsimp } },
  { apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change (nat_trans.mk _ _).app c ≫ (nat_trans.mk _ _).app c = _, hsimp, exact idp },
  { apply nat_trans_eq, apply eq_of_homotopy, intro c, 
    change (nat_trans.mk _ _).app c ≫ (nat_trans.mk _ _).app c = _, hsimp, exact idp } 
end   

@[hott]
def assoc_funct {C D E F : Type _} [is_precat C] [is_precat D] 
  [is_precat E] [is_cat F] (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) : 
  ((G ⋙ H) ⋙ I) = (G ⋙ (H ⋙ I)) := 
@category.isotoid (C ⥤ F) (functor_is_cat) _ _ (assoc_funct_iso G H I)


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
def power_set_precat {A : Set} : is_precat (𝒫 A) :=
  have id_comp : ∀ (B C : 𝒫 A) (f : B ⟶ C), 𝟙 B ≫ f = f, from 
    assume B C f, power_set_unique_hom _ _,
  have comp_id : ∀ (B C : 𝒫 A) (f : B ⟶ C), f ≫ 𝟙 C = f, from 
    assume B C f, power_set_unique_hom _ _,
  have assoc   : ∀ (B C D E : 𝒫 A) (f : B ⟶ C) (g : C ⟶ D) (h : D ⟶ E),
                    (f ≫ g) ≫ h = f ≫ (g ≫ h), from
    assume B C D E f g h, power_set_unique_hom _ _,                   
  is_precat.mk id_comp comp_id assoc

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
def subset_precat_precat {A : Set.{u}} [hA : is_precat.{v} A] 
  (B : Subset A) : is_precat ↥B :=
is_precat.mk (λ (b c : ↥B) (f : b ⟶ c), is_precat.id_comp f) 
               (λ (b c : ↥B) (f : b ⟶ c), is_precat.comp_id f) 
               (λ (b c d e: ↥B) (f : b ⟶ c) (g : c ⟶ d) (h : d ⟶ e), 
                  is_precat.assoc f g h) 

/- The inclusion of two subsets of a set that is a precategory 
   defines a functor between the underlying sets. 

   We need two equalities easily shown by induction. -/ 
@[hott]
def tr_tr_cat_id {C : Type _} [is_precat C] {c c' : C} (p : c = c') : 
  p ▸[λ d, c' ⟶ d] (p ▸[λ d, d ⟶ c] 𝟙 c) = 𝟙 c' :=
begin hinduction p, refl end   

@[hott]
def tr_tr_cat_comp {C : Type _} [is_precat C] {c₁ c₁' c₂ c₂' c₃ c₃': C} (p : c₁ = c₁') 
  (q : c₂ = c₂') (r : c₃ = c₃') (f : c₁' ⟶ c₂') (g : c₂' ⟶ c₃') : 
  r ▸[λ d, c₁' ⟶ d] (p ▸[λ d, d ⟶ c₃] ((p⁻¹ ▸[λ d, d ⟶ c₂] (q⁻¹ ▸[λ d, c₁' ⟶ d] f)) ≫ 
                                         (q⁻¹ ▸[λ d, d ⟶ c₃] (r⁻¹ ▸[λ d, c₂' ⟶ d] g)))) = f ≫ g :=
begin hinduction p, hinduction q, hinduction r, refl end

@[hott]
def functor_subsets_precat {A : Set.{u}} [hA : is_precat.{v} A] {B C : Subset A} 
  (inc : B ⊆ C) : ↥B ⥤ ↥C :=
begin 
  fapply precategories.functor.mk, 
  { intro b, exact ⟨b.1, inc b.1 b.2⟩ }, 
  { intros b b' f, exact f },
  { intro b, refl },
  { intros b₁ b₂ b₃ f g, refl }
end                     


end categories

end hott