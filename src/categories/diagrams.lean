import sets.algebra init2 sets.axioms sets.theories categories.basic categories.adjoints

universes v v' u u' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc hott.is_equiv hott.equiv hott.categories
     hott.categories.adjoints 

namespace categories

/- Precategories whose type of objects is a set are called `strict categories` following 
   the [HoTT-Book,Ch.9.6], but they do not need to be categories. Thus we allow diagrams 
   with loops, that is cycles of homomorphisms that always yield the identity 
   homomorphism when composed. 
  
   Strict categories together with functors between them form a category. In particular, 
   equality of functors between strict categories is unique.  -/
@[hott]
structure strict_category :=
  (obj : Set.{u})
  (precat : precategory.{v} obj)

attribute [instance] strict_category.precat

@[hott, instance]
def functors_of_strict_cat_is_set (D₁ D₂ : strict_category) : 
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
def strict_cat_has_hom : has_hom (strict_category) :=
  has_hom.mk (λ D₁ D₂ : strict_category, Set.mk (D₁.obj ⥤ D₂.obj) 
                                            (functors_of_strict_cat_is_set D₁ D₂))     

@[hott, instance]
def strict_cat_cat_str : category_struct strict_category :=
  category_struct.mk (λ D, id_functor D.obj) (λ D₁ D₂ D₃ F G, F ⋙ G)

@[hott, instance]
def strict_cat_precat : precategory strict_category :=
precategory.mk (λ D₁ D₂ F, funct_id_comp F) 
               (λ D₁ D₂ F, funct_comp_id F) 
               (λ D₁ D₂ D₃ D₄ F G H, funct_comp_assoc F G H)

namespace strict_cat

/- In the [HoTT-Book], three types of equivalences between (pre)categories are discussed :
   equivalences of (pre)categories [Def.9.4.1], isomorphisms of (pre)categories [Def.9.4.8]
   and equalities. They only are equivalent types if the precategories are categories 
   [Lem.9.4.15/16]. 
   
   However, from an isomorphism in the category of strict categories we can deduce an 
   isomorphism of precategories in the sense of [Def.9.4.8], and this allows us to 
   construct `isotoid` making `idtoiso` an equivalence in the precategory of strict 
   categories. 
   
   The construction of the equivalence is organised in 3 steps:
   The first step is to split up equalities of strict precategories in components and to 
   show that equalities of the components is equivalent to equality of the strict 
   precategories. -/ 
@[hott]
structure comp_eq (D₁ D₂ : strict_category) :=
  (Pₒ : D₁.obj = D₂.obj)  
  (Pₕ : Π a b : D₁.obj, (a ⟶ b) = (Pₒ ▸[(λ (A : Set), A.carrier)] a ⟶ 
                                                 Pₒ ▸[(λ (A : Set), A.carrier)] b))
  (id_eq : Π a : D₁.obj, (Pₕ a a) ▸ 𝟙 a = 𝟙 (Pₒ ▸ a))
  (comp_hom_eq : Π (a b c : D₁.obj) (f : a ⟶ b) (g : b ⟶ c), (Pₕ a c) ▸ (f ≫ g) = 
                            ((Pₕ a b) ▸ f) ≫ ((Pₕ b c) ▸ g))                                               

@[hott]
def comp_eq_eta {D₁ D₂ : strict_category} (eq : comp_eq D₁ D₂) :
  eq = comp_eq.mk eq.Pₒ eq.Pₕ eq.id_eq eq.comp_hom_eq :=
begin hinduction eq, hsimp end   

@[hott]
def idp_comp_eq (D : strict_category) : comp_eq D D :=
begin 
  fapply comp_eq.mk,
  { exact idp },
  { intros a b, hsimp },
  { intro a, hsimp },
  { intros a b c f g, hsimp } 
end

@[hott, hsimp]
def eq_to_comp_eq (D₁ D₂ : strict_category) : 
  D₁ = D₂ -> comp_eq D₁ D₂ :=
begin
  intro p, hinduction p, fapply comp_eq.mk, 
  { exact idp },
  { intros a b, hsimp },
  { intro a, hsimp },
  { intros a b c f g, hsimp }
end    

@[hott]
def eq_to_comp_eq_obj {D₁ D₂ : strict_category} (eq : D₁ = D₂) :
  ap strict_category.obj eq = (eq_to_comp_eq D₁ D₂ eq).Pₒ :=
begin hinduction eq, hsimp end

@[hott]
def eq_to_comp_eq_hom {D₁ D₂ : strict_category} (eq : D₁ = D₂) :
  (eq_to_comp_eq D₁ D₂ eq).Pₕ = 
  λ a b : D₁.obj, @eq.rec _ _ (λ (D : strict_category) (p : D₁ = D), 
            (a ⟶ b) = ((eq_to_comp_eq D₁ D p).Pₒ ▸ a ⟶ 
                        (eq_to_comp_eq D₁ D p).Pₒ ▸ b)) 
            (@idp _ (a ⟶ b)) D₂ eq :=
begin hinduction eq, exact rfl end

@[hott]
def eq_to_comp_eq_idp (D : strict_category) :
  eq_to_comp_eq D D (idpath D) = idp_comp_eq D :=
begin rwr comp_eq_eta (eq_to_comp_eq D D (idpath D)) end  

@[hott]
def comp_eq_to_eq (D₁ D₂ : strict_category) : 
  comp_eq D₁ D₂ -> D₁ = D₂ :=
begin
  hinduction D₁ with obj₁ precat₁, hinduction D₂ with obj₂ precat₂, 
  intro comp_eq, hinduction comp_eq with Pₒ Pₕ id_eq comp_eq, change obj₁ = obj₂ at Pₒ, 
  hinduction Pₒ, fapply apd011 strict_category.mk, 
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

@[hott]
def comp_eq_to_eq_obj {D₁ D₂ : strict_category} (ceq : comp_eq D₁ D₂) :
  (eq_to_comp_eq D₁ D₂ (comp_eq_to_eq D₁ D₂ ceq)).Pₒ = ceq.Pₒ :=
begin 
  hinduction ceq, hinduction D₁ with obj₁ precat₁, hinduction D₂ with obj₂ precat₂, 
  change obj₁ = obj₂ at Pₒ, hinduction Pₒ, rwr <- eq_to_comp_eq_obj,
  change ap strict_category.obj (apd011 strict_category.mk _ _) = @idp _ obj₁, 
  let H : Π (o : Set) (p : precategory ↥o), strict_category.obj (strict_category.mk o p) = o := 
    assume o p, idp,
  rwr ap_apd011 _ _ _ _ H 
end  

@[hott]
def comp_eq_to_eq_hom {D₁ D₂ : strict_category} (ceq : comp_eq D₁ D₂) :
  (eq_to_comp_eq D₁ D₂ (comp_eq_to_eq D₁ D₂ ceq)).Pₕ =[comp_eq_to_eq_obj ceq; 
          λ (P : D₁.obj = D₂.obj), Π (a b : D₁.obj), (a ⟶ b) = (P ▸ a ⟶ P ▸ b)] ceq.Pₕ :=
begin
  apply pathover_of_tr_eq, apply eq_of_homotopy2, intros a b, 
  hinduction ceq, change _ = Pₕ a b,
  hinduction D₁ with obj₁ precat₁, hinduction D₂ with obj₂ precat₂, 
  change obj₁ = obj₂ at Pₒ, hinduction Pₒ,
  sorry
end  

@[hott]
def comp_eq_to_eq_idp (D : strict_category) : comp_eq_to_eq D D (idp_comp_eq D) = refl D :=
begin 
  change comp_eq_to_eq D D (comp_eq.mk _ _ _ _) = _, 
  hinduction D with obj precat, 
  change apd011 strict_category.mk _ _ = apd011 strict_category.mk idp idpo,
  fapply apd011 (apd011 strict_category.mk), 
  { refl }, 
  { apply pathover_of_tr_eq, change _ = pathover_idp_of_eq _ idp, 
    apply ap (pathover_idp_of_eq _), hinduction precat with cat_struct id_comp comp_id assoc,
    hsimp, sorry }
end  

@[hott]
def eq_eqv_comp_eq (D₁ D₂ : strict_category) : D₁ = D₂ ≃ comp_eq D₁ D₂ :=
begin
  fapply equiv.mk, 
  { exact eq_to_comp_eq D₁ D₂ },
  { fapply adjointify, 
    { exact comp_eq_to_eq D₁ D₂ },
    { intro b, hinduction b, rwr comp_eq_eta (eq_to_comp_eq D₁ D₂ _),
      fapply apd01111_v2 comp_eq.mk, 
      { rwr comp_eq_to_eq_obj },
      { change _ =[_ ▸[λ P, P = Pₒ] idp] _, rwr id_tr_eq_id_inv_con, rwr con_idp, 
        rwr hott.eq.inv_inv, 
        exact @comp_eq_to_eq_hom D₁ D₂ (comp_eq.mk Pₒ Pₕ id_eq comp_hom_eq) },
      { apply pathover_of_tr_eq, apply eq_of_homotopy, intro a, exact is_set.elim _ _ },
      { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b c, 
        apply eq_of_homotopy2, intros f g, exact is_set.elim _ _ } },
    { intro p, hinduction p, rwr eq_to_comp_eq_idp, 
      exact comp_eq_to_eq_idp D₁ } }
end                               
  
/- Next, we adjointify the two natural transformations given by an isomorphism of two 
   precategories, as in [HoTT-Book,Lem.9.4.2]. This gives an equivalence of precategories. -/
@[hott]
def strict_cat_iso_to_obj_eqv : 
  Π {D₁ D₂ : strict_category}, (D₁ ≅ D₂) -> (D₁.obj ≃ D₂.obj) :=
assume D₁ D₂ iD, equiv.mk iD.hom.obj (adjointify iD.hom.obj iD.inv.obj 
                                     (homotopy_of_eq (ap functor.obj iD.r_inv)) 
                                     (homotopy_of_eq (ap functor.obj iD.l_inv)))

@[hott]
def strict_cat_iso_to_obj_eq : 
  Π {D₁ D₂ : strict_category}, (D₁ ≅ D₂) -> (D₁.obj = D₂.obj) :=
assume D₁ D₂ iD, car_eq_to_set_eq (ua (strict_cat_iso_to_obj_eqv iD))                                                 

@[hott] 
def strict_cat_obj_tr_iso {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂) :
  Π d₁ : D₁.obj, (strict_cat_iso_to_obj_eq iD) ▸ d₁ = iD.hom.obj d₁ :=
begin
  intro d₁, 
  change (strict_cat_iso_to_obj_eq iD) ▸[λ A : Set, A.carrier] d₁ = iD.hom.obj d₁, 
  rwr @tr_ap_id Set (λ A : Set, A.carrier) _ _ (strict_cat_iso_to_obj_eq iD) d₁,
  change (set_eq_to_car_eq (car_eq_to_set_eq _)) ▸[λ D, D] d₁ = _, 
  rwr rinv_set_eq_car_eq, change cast (ua (strict_cat_iso_to_obj_eqv iD)) d₁ = _,
  rwr cast_ua
end  

@[hott]
def strict_cat_iso_to_unit_iso : 
  Π {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂), (iD.hom ⋙ iD.inv) ≅ id_functor D₁.obj :=
assume D₁ D₂ iD, idtoiso iD.l_inv

@[hott]
def strict_cat_iso_to_counit_iso_hom : 
  Π {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂), id_functor D₂.obj ⟹ (iD.inv ⋙ iD.hom) :=
begin
  intros D₁ D₂ iD, 
  let η := strict_cat_iso_to_unit_iso iD, 
  let ε : id_functor ↥(D₂.obj) ≅ iD⁻¹ʰ ≫ iD.hom := inv_iso (idtoiso iD.r_inv),
  fapply nat_trans.mk, 
  { intro d₂, exact ε.hom.app d₂ ≫ iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂)) ≫ 
                    ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj (d₂))) },
  { intros d₂ d₂' g,
    calc (id_functor ↥(D₂.obj)).map g ≫ ε.hom.app d₂' ≫ 
          iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂')) ≫ ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj d₂')) = 
               ((id_functor ↥(D₂.obj)).map g ≫ ε.hom.app d₂') ≫ 
                 iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂')) ≫ 
                 ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj d₂')) : by rwr <- precategory.assoc
         ... = (ε.hom.app d₂ ≫ iD.hom.map (iD⁻¹ʰ.map g)) ≫ 
                iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂')) ≫ 
                ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj d₂')) : by rwr ε.hom.naturality
         ... = ε.hom.app d₂ ≫ iD.hom.map (iD⁻¹ʰ.map g) ≫ 
               iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂')) ≫ 
               ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj d₂')) : by rwr precategory.assoc;       
                                                          rwr precategory.assoc
         ... = ε.hom.app d₂ ≫ iD.hom.map ((id_functor ↥(D₁.obj)).map (iD⁻¹ʰ.map g) ≫ 
               η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂')) ≫ _ : by hsimp
         ... = _ ≫ iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂) ≫ 
                   iD⁻¹ʰ.map (iD.hom.map (iD⁻¹ʰ.map g))) ≫ _ : by rwr η⁻¹ʰ.naturality
         ... = _ ≫ (iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂)) ≫ 
                    iD.hom.map (iD⁻¹ʰ.map (iD.hom.map (iD⁻¹ʰ.map g)))) ≫ _ : by hsimp
         ... = _ ≫ _ ≫ iD.hom.map (iD⁻¹ʰ.map (iD.hom.map (iD⁻¹ʰ.map g))) ≫ 
                        ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj d₂')) : by rwr precategory.assoc
         ... = _ ≫ _ ≫ (iD⁻¹ʰ ≫ iD.hom).map (iD.hom.map (iD⁻¹ʰ.map g)) ≫ 
                        ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj d₂')) : idp                
         ... = _ ≫ _ ≫ ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) ≫ iD.hom.map (iD⁻¹ʰ.map g) :                        
               by rwr ε⁻¹ʰ.naturality
         ... = (ε.hom.app d₂ ≫ iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂)) ≫ 
                ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj d₂))) ≫ (iD⁻¹ʰ ⋙ iD.hom).map g : 
                by rwr <- precategory.assoc; rwr <- precategory.assoc;
                   rwr precategory.assoc (ε.hom.app d₂)               }
end 

@[hott]
def strict_cat_iso_to_counit_iso_inv : 
  Π {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂), (iD.inv ⋙ iD.hom) ⟹ id_functor D₂.obj :=
begin
  intros D₁ D₂ iD, 
  let η := strict_cat_iso_to_unit_iso iD, 
  let ε : id_functor ↥(D₂.obj) ≅ iD⁻¹ʰ ≫ iD.hom := inv_iso (idtoiso iD.r_inv),
  fapply nat_trans.mk, 
  { intro d₂, exact ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) ≫ 
                    iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂)) ≫ ε⁻¹ʰ.app d₂ },
  { intros d₂ d₂' g,
    calc (iD⁻¹ʰ ⋙ iD.hom).map g ≫ ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj (d₂'))) ≫ 
                    iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂')) ≫ ε⁻¹ʰ.app d₂' = 
               ((iD⁻¹ʰ ⋙ iD.hom).map g ≫ ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj (d₂')))) ≫ 
                 iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂')) ≫ 
                 ε⁻¹ʰ.app d₂' : by rwr <- precategory.assoc
         ... = (ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) ≫ 
                iD.hom.map (iD⁻¹ʰ.map (iD.hom.map (iD⁻¹ʰ.map g)))) ≫ 
                iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂')) ≫ ε⁻¹ʰ.app d₂' : by rwr ε.hom.naturality
         ... =  ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) ≫ 
                (iD.hom.map (iD⁻¹ʰ.map (iD.hom.map (iD⁻¹ʰ.map g))) ≫ 
                iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂'))) ≫ ε⁻¹ʰ.app d₂' : 
               by rwr precategory.assoc; rwr precategory.assoc
         ... = ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) ≫ 
                iD.hom.map (iD⁻¹ʰ.map (iD.hom.map (iD⁻¹ʰ.map g)) ≫ 
                            η.hom.app (iD⁻¹ʰ.obj d₂')) ≫ ε⁻¹ʰ.app d₂' : by hsimp
         ... = _ ≫ iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂) ≫ 
                   (id_functor ↥(D₁.obj)).map (iD⁻¹ʰ.map g)) ≫ _ : by rwr η.hom.naturality
         ... = _ ≫ (iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂)) ≫ 
                    iD.hom.map (iD⁻¹ʰ.map g)) ≫ _ : by hsimp
         ... = _ ≫ _ ≫ iD.hom.map (iD⁻¹ʰ.map g) ≫ ε⁻¹ʰ.app d₂' : by rwr precategory.assoc
         ... = _ ≫ _ ≫ (iD⁻¹ʰ ≫ iD.hom).map g ≫ ε⁻¹ʰ.app d₂' : idp                
         ... = _ ≫ _ ≫ ε⁻¹ʰ.app d₂ ≫ (id_functor ↥(D₂.obj)).map g : by rwr ε⁻¹ʰ.naturality
         ... = (ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) ≫ 
                iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂)) ≫ ε⁻¹ʰ.app d₂) ≫ g : 
                by rwr <- precategory.assoc; rwr <- precategory.assoc;
                   rwr precategory.assoc (ε.hom.app _)               }
end 

@[hott]
def strict_cat_iso_to_counit_iso : 
  Π {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂), id_functor D₂.obj ≅ (iD.inv ⋙ iD.hom) :=
begin
  intros D₁ D₂ iD, 
  let η := strict_cat_iso_to_unit_iso iD, let ε := inv_iso (idtoiso iD.r_inv),
  fapply iso.mk, 
  { exact strict_cat_iso_to_counit_iso_hom iD },
  { exact strict_cat_iso_to_counit_iso_inv iD },
  { apply nat_trans_eq, apply eq_of_homotopy, intro d₂,
    change (ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) ≫ iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂)) 
           ≫ ε⁻¹ʰ.app d₂) ≫ (ε.hom.app d₂ ≫ iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂)) ≫ 
          ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj (d₂)))) = 𝟙 (iD.hom.obj (iD⁻¹ʰ.obj d₂)), 
    rwr precategory.assoc, rwr <- precategory.assoc _ (ε.hom.app d₂) _, 
    rwr precategory.assoc _ _ (ε.hom.app d₂), 
    change _ ≫ (_ ≫ (ε⁻¹ʰ ≫ ε.hom).app d₂) ≫ _ ≫ _ = _, rwr ap nat_trans.app ε.r_inv,
    change _ ≫ (_ ≫ 𝟙 ((iD⁻¹ʰ ≫ iD.hom).obj d₂)) ≫ _ ≫ _ = _, rwr precategory.comp_id, 
    rwr <- precategory.assoc (iD.hom.map _), rwr <- functor.map_comp, 
    change _ ≫ iD.hom.map ((η.hom ≫ η⁻¹ʰ).app (iD⁻¹ʰ.obj d₂)) ≫ _ = _, 
    rwr ap nat_trans.app η.l_inv, change _ ≫ iD.hom.map (𝟙 _) ≫ _ = _, rwr functor.map_id, 
    rwr precategory.id_comp, change (ε.hom ≫ ε⁻¹ʰ).app _ = _, rwr ap nat_trans.app ε.l_inv },
  { apply nat_trans_eq, apply eq_of_homotopy, intro d₂,
    change (ε.hom.app d₂ ≫ iD.hom.map (η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂)) ≫ 
          ε⁻¹ʰ.app (iD.hom.obj (iD⁻¹ʰ.obj (d₂)))) ≫ (ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) ≫ iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂)) 
           ≫ ε⁻¹ʰ.app d₂) = 𝟙 d₂, 
    rwr precategory.assoc, rwr <- precategory.assoc _ (ε.hom.app _) _, 
    rwr precategory.assoc _ _ (ε.hom.app _), 
    change _ ≫ (_ ≫ (ε⁻¹ʰ ≫ ε.hom).app _) ≫ _ ≫ _ = _, rwr ap nat_trans.app ε.r_inv,
    change _ ≫ (_ ≫ 𝟙 ((iD⁻¹ʰ ≫ iD.hom).obj _)) ≫ _ ≫ _ = _, rwr precategory.comp_id,
    rwr <- precategory.assoc (iD.hom.map _), rwr <- functor.map_comp, 
    change _ ≫ iD.hom.map ((η⁻¹ʰ ≫ η.hom).app _) ≫ _ = _, 
    rwr ap nat_trans.app η.r_inv, change _ ≫ iD.hom.map (𝟙 _) ≫ _ = _, rwr functor.map_id, 
    rwr precategory.id_comp, change (ε.hom ≫ ε⁻¹ʰ).app _ = _, rwr ap nat_trans.app ε.l_inv }
end  

@[hott]
def strict_cat_iso_adj {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂) : 
  adjoint_functors iD.hom iD.inv :=
begin
  let η := strict_cat_iso_to_unit_iso iD, let ε := inv_iso (idtoiso iD.r_inv),
  let ε' := strict_cat_iso_to_counit_iso iD,
  have H : Π d₁ : D₁.obj, η.hom.app (iD⁻¹ʰ.obj (iD.hom.obj d₁)) = 
                                             iD⁻¹ʰ.map (iD.hom.map (η.hom.app d₁)), from
    begin 
      intro d₁, rwr <- precategory.comp_id (η.hom.app (iD⁻¹ʰ.obj (iD.hom.obj d₁))), 
      rwr <- precategory.comp_id (iD⁻¹ʰ.map (iD.hom.map (η.hom.app d₁))),  
      change η.hom.app (iD⁻¹ʰ.obj (iD.hom.obj d₁)) ≫ (𝟙 (iD.hom ⋙ iD⁻¹ʰ)).app d₁ =
             iD⁻¹ʰ.map (iD.hom.map (η.hom.app d₁)) ≫ (𝟙 (iD.hom ⋙ iD⁻¹ʰ)).app d₁, 
      rwr <- apd10 (ap nat_trans.app η.l_inv) d₁, 
      change η.hom.app (iD⁻¹ʰ.obj (iD.hom.obj d₁)) ≫ η.hom.app d₁ ≫ η⁻¹ʰ.app d₁ =
             iD⁻¹ʰ.map (iD.hom.map (η.hom.app d₁)) ≫ η.hom.app d₁ ≫ η⁻¹ʰ.app d₁,
      rwr <- precategory.assoc, rwr <- precategory.assoc, 
      rwr η.hom.naturality (η.hom.app d₁)
    end,
  have H' : Π d₂ : D₂.obj, ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) = 
                                             iD.hom.map (iD⁻¹ʰ.map (ε.hom.app d₂)), from
    begin 
      intro d₂, rwr <- precategory.id_comp (ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂))), 
      rwr <- precategory.id_comp (iD.hom.map (iD⁻¹ʰ.map (ε.hom.app d₂))),        
      change (nat_trans_id (iD⁻¹ʰ ⋙ iD.hom)).app d₂ ≫ _ = 
             (nat_trans_id (iD⁻¹ʰ ⋙ iD.hom)).app d₂ ≫ _, 
      have p : nat_trans_id (iD⁻¹ʰ ⋙ iD.hom) = 𝟙 (iD⁻¹ʰ ≫ iD.hom), from idp, rwr p,      
      rwr <- apd10 (ap nat_trans.app ε.r_inv) d₂, 
      change (ε⁻¹ʰ.app d₂ ≫ ε.hom.app d₂) ≫ _ = (ε⁻¹ʰ.app d₂ ≫ ε.hom.app d₂) ≫ _,
      rwr precategory.assoc, rwr precategory.assoc, 
      let p' : ε.hom.app d₂ ≫ ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) =
                  ε.hom.app d₂ ≫ iD.hom.map (iD⁻¹ʰ.map (ε.hom.app d₂)) := 
               ε.hom.naturality (ε.hom.app d₂), rwr p'
    end,  
  fapply adjoint_functors.mk, 
  { exact η.inv },
  { exact ε'.inv },
  { intro d₁, 
    change _ ≫ ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj (iD.hom.obj d₁))) ≫ 
      iD.hom.map (η.hom.app (iD⁻¹ʰ.obj (iD.hom.obj d₁))) ≫ ε⁻¹ʰ.app (iD.hom.obj d₁) = _,
    rwr H d₁, change _ ≫ _ ≫ (iD⁻¹ʰ ≫ iD.hom).map (iD.hom.map (η.hom.app d₁)) ≫
                     ε⁻¹ʰ.app (iD.hom.obj ((id_functor ↥(D₁.obj)).obj d₁)) = _,
    rwr ε⁻¹ʰ.naturality (iD.hom.map (η.hom.app d₁)), 
    change _ ≫ _ ≫ _ ≫ iD.hom.map (η.hom.app d₁) = _,
    rwr <- precategory.assoc _ _ (iD.hom.map (η.hom.app d₁)), 
    change _ ≫ ((ε.hom ≫ ε⁻¹ʰ).app _) ≫ _ = _, rwr ap nat_trans.app ε.l_inv, 
    change _ ≫ 𝟙 (iD.hom.obj ((iD.hom ⋙ iD⁻¹ʰ).obj d₁)) ≫ _ = _, 
    rwr precategory.id_comp, rwr <- functor.map_comp, 
    change iD.hom.map ((η⁻¹ʰ ≫ η.hom).app d₁) = _, rwr ap nat_trans.app η.r_inv, hsimp },
  { intro d₂, 
    change _ ≫ iD⁻¹ʰ.map (ε.hom.app (iD.hom.obj (iD⁻¹ʰ.obj d₂)) ≫ 
                           iD.hom.map (η.hom.app (iD⁻¹ʰ.obj d₂)) ≫ ε⁻¹ʰ.app d₂) = _, 
    rwr functor.map_comp, rwr functor.map_comp,       
    rwr H' d₂, rwr <- H (iD⁻¹ʰ.obj d₂),
    change _ ≫ (iD.hom ≫ iD⁻¹ʰ).map (iD⁻¹ʰ.map (ε.hom.app d₂)) ≫ _ ≫ _ = _,
    rwr <- precategory.assoc, 
    let p : _ = η⁻¹ʰ.app (iD⁻¹ʰ.obj d₂) ≫ (iD.hom ≫ iD⁻¹ʰ).map (iD⁻¹ʰ.map (ε.hom.app d₂)) 
          := η⁻¹ʰ.naturality (iD⁻¹ʰ.map (ε.hom.app d₂)), rwr <- p, 
    rwr precategory.assoc, rwr <- precategory.assoc _ _ (iD⁻¹ʰ.map (ε⁻¹ʰ.app d₂)), 
    change _ ≫ (η⁻¹ʰ ≫ η.hom).app _ ≫ _ = _, rwr ap nat_trans.app η.r_inv,
    change _ ≫ 𝟙 (iD⁻¹ʰ.obj ((iD⁻¹ʰ ≫ iD.hom).obj d₂)) ≫ _ = _, rwr precategory.id_comp,
    change iD⁻¹ʰ.map (ε.hom.app d₂) ≫ iD⁻¹ʰ.map (ε⁻¹ʰ.app d₂) = _, 
    rwr <- functor.map_comp, change iD⁻¹ʰ.map ((ε.hom ≫ ε⁻¹ʰ).app d₂) = _, 
    rwr ap nat_trans.app ε.l_inv, change iD⁻¹ʰ.map (𝟙 d₂) = _, rwr functor.map_id }
end

/- Now we can use the triangle identities to construct a bijection between sets of 
   homomorphisms from isomorphisms of strict categories. -/
@[hott]
def strict_cat_iso_to_fully_faithful : Π {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂), 
  Π (a b : D₁.obj), bijection (a ⟶ b) (functor.obj iD.hom a ⟶ functor.obj iD.hom b) :=
begin
  intros D₁ D₂ iD a b, 
  let η := strict_cat_iso_to_unit_iso iD, let ε := strict_cat_iso_to_counit_iso iD,
  fapply has_inverse_to_bijection, 
  { exact λ f : a ⟶ b, iD.hom.map f },
  { intro g, exact η⁻¹ʰ.app a ≫ iD.inv.map g ≫ η.hom.app b },
  { fapply is_set_inverse_of.mk,
    { intro g, hsimp, 
      have p : iD.hom.map (η.hom.app b) = ε⁻¹ʰ.app (iD.hom.obj b), from 
        calc _ = iD.hom.map (η.hom.app b) ≫ 𝟙 _ : by rwr <- precategory.comp_id
             ... = iD.hom.map (η.hom.app b) ≫ iD.hom.map (η⁻¹ʰ.app b) ≫ 
                                             ε⁻¹ʰ.app (iD.hom.obj b) : 
                   by rwr <- (strict_cat_iso_adj iD).zigzag_L
             ... = (iD.hom.map (η.hom.app b) ≫ iD.hom.map (η⁻¹ʰ.app b)) ≫ 
                                             ε⁻¹ʰ.app (iD.hom.obj b) : 
                   by rwr precategory.assoc 
             ... = iD.hom.map ((η.hom ≫ η⁻¹ʰ).app b) ≫ ε⁻¹ʰ.app (iD.hom.obj b) : by hsimp
             ... = iD.hom.map (𝟙 ((iD.hom ⋙ iD⁻¹ʰ).obj b)) ≫ ε⁻¹ʰ.app (iD.hom.obj b) : 
                   by rwr ap nat_trans.app η.l_inv 
             ... = 𝟙 (iD.hom.obj ((iD.hom ⋙ iD⁻¹ʰ).obj b)) ≫ ε⁻¹ʰ.app (iD.hom.obj b) : 
                   by rwr functor.map_id                                                                   
             ... = _ : by rwr precategory.id_comp,
      rwr p, rwr ε⁻¹ʰ.naturality, 
      have p' : iD.hom.map (η⁻¹ʰ.app a) = ε.hom.app (iD.hom.obj a), from 
        calc _ = iD.hom.map (η⁻¹ʰ.app a) ≫ 𝟙 _ : by rwr precategory.comp_id
             ... = iD.hom.map (η⁻¹ʰ.app a) ≫ (ε⁻¹ʰ ≫ ε.hom).app (iD.hom.obj a) : 
                   by rwr ap nat_trans.app ε.r_inv
             ... = iD.hom.map (η⁻¹ʰ.app a) ≫ ε⁻¹ʰ.app (iD.hom.obj a) ≫ 
                   ε.hom.app (iD.hom.obj a) : by refl
             ... = (iD.hom.map (η⁻¹ʰ.app a) ≫ ε⁻¹ʰ.app (iD.hom.obj a)) ≫ 
                   ε.hom.app (iD.hom.obj a) : by rwr precategory.assoc  
             ... = 𝟙 (iD.hom.obj a) ≫ ε.hom.app (iD.hom.obj a) : 
                   by rwr <- (strict_cat_iso_adj iD).zigzag_L                
             ... = _ : by rwr precategory.id_comp,
      rwr p', rwr <- precategory.assoc, change (ε.hom ≫ ε⁻¹ʰ).app (iD.hom.obj a) ≫ _ = _, 
      rwr ap nat_trans.app ε.l_inv, hsimp },
    { intro f, hsimp, rwr η.hom.naturality, rwr <- precategory.assoc, 
      change (η⁻¹ʰ ≫ η.hom).app _ ≫ _ = _, rwr ap nat_trans.app η.r_inv, hsimp } },
end

@[hott, reducible]
def strict_cat_isotoid : Π {D₁ D₂ : strict_category}, (D₁ ≅ D₂) -> (D₁ = D₂) :=
begin  
  intros D₁ D₂ iD, fapply strict_cat_eq, 
  { exact strict_cat_iso_to_obj_eq iD },
  { intros a b, 
    have p : (strict_cat_iso_to_obj_eq iD ▸ a ⟶ strict_cat_iso_to_obj_eq iD ▸ b) =
             (iD.hom.obj a ⟶ iD.hom.obj b), from 
      begin rwr strict_cat_obj_tr_iso iD a, rwr strict_cat_obj_tr_iso iD b end,
    apply (λ q, eq.concat q p⁻¹), 
    exact bij_to_set_eq (strict_cat_iso_to_fully_faithful iD a b) },
  { intro a, 
    change ((bij_to_set_eq (strict_cat_iso_to_fully_faithful iD a a)) ⬝ _) ▸ 𝟙 a =_,
    rwr con_tr, rwr <- bij_hom_tr_eq, change _ ▸ iD.hom.map (𝟙 a) = _, 
    rwr functor.map_id, 
    have H_id : Π {d₂ d₂' : D₂.obj} (p : d₂ = d₂'), 
           (p⁻¹ ▸[λ d : D₂.obj, (d ⟶ d₂) = (d₂' ⟶ d₂')] 
           (p⁻¹ ▸[λ d : D₂.obj, (d₂' ⟶ d) = (d₂' ⟶ d₂')] idp))⁻¹ ▸ (𝟙 d₂') = 𝟙 d₂, from
      begin intros d₂ d₂' p, hinduction p, hsimp end,  
    rwr H_id },
  { intros a b c f g, 
    change ((bij_to_set_eq (strict_cat_iso_to_fully_faithful iD a c)) ⬝ _) ▸ f ≫ g =
           (((bij_to_set_eq (strict_cat_iso_to_fully_faithful iD a b)) ⬝ _) ▸ f) ≫
           (((bij_to_set_eq (strict_cat_iso_to_fully_faithful iD b c)) ⬝ _) ▸ g),
    rwr con_tr, rwr con_tr, rwr con_tr, rwr <- bij_hom_tr_eq, rwr <- bij_hom_tr_eq,
    rwr <- bij_hom_tr_eq, 
    change _ ▸ iD.hom.map (f ≫ g) = (_ ▸ iD.hom.map f) ≫ (_ ▸ iD.hom.map g), 
    rwr functor.map_comp,
    have H_comp : Π {a b c a' b' c' : D₂.obj} (pa : a = a') (pb : b = b') (pc : c = c')
           (f : a' ⟶ b') (g : b' ⟶ c'), (pa⁻¹ ▸[λ d : D₂.obj, (d ⟶ c) = (a' ⟶ c')] 
           (pc⁻¹ ▸[λ d : D₂.obj, (a' ⟶ d) = (a' ⟶ c')] idp))⁻¹ ▸ (f ≫ g) =
           ((pa⁻¹ ▸[λ d : D₂.obj, (d ⟶ b) = (a' ⟶ b')] 
           (pb⁻¹ ▸[λ d : D₂.obj, (a' ⟶ d) = (a' ⟶ b')] idp))⁻¹ ▸ f) ≫
           ((pb⁻¹ ▸[λ d : D₂.obj, (d ⟶ c) = (b' ⟶ c')] 
           (pc⁻¹ ▸[λ d : D₂.obj, (b' ⟶ d) = (b' ⟶ c')] idp))⁻¹ ▸ g), from 
      begin intros, hinduction pa, hinduction pb, hinduction pc, hsimp end,
    rwr H_comp }
end    

@[hott]
def strict_cat_isotoid_idfunct_obj_eq {D₁ D₂ : strict_category} (i : D₁ ≅ D₂) : 
  (strict_cat_isotoid i ▸[λ D : strict_category, D₁.obj ⥤ D.obj] 
                                               id_functor ↥(D₁.obj)).obj = i.hom.obj :=
begin
  change (λ D : strict_category, @functor.obj D₁.obj D.obj _ _) D₂ 
                (strict_cat_isotoid i ▸[λ D : strict_category, D₁.obj ⥤ D.obj] 
                id_functor (D₁.obj)) = _,
  rwr fn_tr_tr_ev (λ D : strict_category, @functor.obj D₁.obj D.obj _ _), 
  apply tr_eq_of_pathover, apply pathover_of_pathover_ap (λ D : Set, D₁.obj -> D), 
  apply pathover_of_tr_eq, rwr strict_cat_eq_obj_eta, apply eq_of_homotopy, intro d₁,
  rwr tr_fn_eval_tr', rwr strict_cat_obj_tr_iso
end                                                 

@[hott]
def strict_cat_isotoid_idfunct {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂) :=
  strict_cat_isotoid iD ▸[λ D : strict_category, D₁.obj ⥤ D.obj] id_functor ↥(D₁.obj)

@[hott]
def strict_cat_isotoid_idfunct_map {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂) :=  
  λ a b : D₁.obj, @functor.map _ _ _ _ (strict_cat_isotoid_idfunct iD) a b  

@[hott]
def strict_cat_isotoid_idfunct_map_eq {D₁ D₂ : strict_category} (iD : D₁ ≅ D₂) :
  strict_cat_isotoid_idfunct_map iD =[strict_cat_isotoid_idfunct_obj_eq iD;
                     λ f : D₁.obj -> D₂.obj, Π (a b : D₁.obj), (a ⟶ b) -> (f a ⟶ f b)]
            iD.hom.map :=
begin
  apply pathover_of_tr_eq,   
  --rwr apdt, apply eq_of_homotopy3, intros a b f, 
  sorry
end  

end strict_cat

@[hott, instance]
def strict_cat_cat : category strict_category :=
begin
  apply category.mk, intros D₁ D₂, fapply adjointify,
  { exact strict_cat_isotoid },
  { intro iD, change strict_cat_isotoid iD ▸ (id_is_iso D₁) = iD, apply hom_eq_to_iso_eq,
    rwr fn2_tr_tr_ev (@iso.hom _ _), 
    change strict_cat_isotoid iD ▸[λ D : strict_category, D₁.obj ⥤ D.obj] 
                                                                    id_functor D₁.obj = _,  
    fapply functor_eq, 
    { exact strict_cat_isotoid_idfunct_obj_eq iD },
    { exact strict_cat_isotoid_idfunct_map_eq iD } },
  { intro p, hinduction p, sorry }
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