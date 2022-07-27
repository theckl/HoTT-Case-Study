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
def flat_mk : Π (obj : Set.{u}) (hom : obj -> obj -> Set.{v}) 
  (id : Π a : obj, hom a a) (comp : Π {a b c}, hom a b -> hom b c -> hom a c),
  (Π {a b} (g : hom a b), comp (id a) g = g) ->
  (Π {a b} (f : hom a b), comp f (id b) = f) ->
  (Π {a b c d} (f : hom a b) (g : hom b c) (h : hom c d), 
       comp (comp f g) h = comp f (comp g h)) -> strict_category :=
assume obj hom id comp id_comp comp_id assoc, 
strict_category.mk obj (@precategory.mk ↥obj (@category_struct.mk ↥obj (has_hom.mk hom) 
                                                                  @id @comp) 
                                        @id_comp @comp_id @assoc)     

@[hott, hsimp]
def flat_eta (D : strict_category) : 
  D = flat_mk D.obj D.precat.to_has_hom.hom D.precat.to_category_struct.id 
              D.precat.to_category_struct.comp D.precat.id_comp D.precat.comp_id
              D.precat.assoc :=
begin 
  hinduction D with obj precat, hsimp, 
  hinduction precat with cat_str id_comp comp_id assoc, hsimp,
  hinduction cat_str with has_hom id comp, hinduction has_hom with hom, hsimp,
  exact idp
end              

@[hott]
def ap_obj_flat_eta (D : strict_category) : 
  ap strict_category.obj (flat_eta D) = @idp _ D.obj :=
begin 
  hinduction D with obj precat, hsimp, 
  hinduction precat with cat_str id_comp comp_id assoc, hsimp,
  hinduction cat_str with has_hom id comp, hinduction has_hom with hom, 
  change ap strict_category.obj idp = _, hsimp
end

@[hott]
structure flat_comp_eq (D₁ D₂ : strict_category) :=
  (pₒ : D₁.obj = D₂.obj)
  (pₕ : (λ a b : D₁.obj, a ⟶ b) =[pₒ; λ D : Set, D -> D -> Set] (λ a b : D₂.obj, a ⟶ b))
  (pᵢ : (λ a : D₁.obj, 𝟙 a) =[apd011 (λ (D : Set) (h : D -> D -> Set), Π (a : D), h a a) 
                                     pₒ pₕ; id] (λ a : D₂.obj, 𝟙 a))
  (pc : (λ (a b c: D₁.obj) (f : a ⟶ b) (g : b ⟶ c), f ≫ g) =[apd011 
        (λ (D : Set) (h : D -> D -> Set), Π (a b c : D), h a b -> h b c -> h a c) 
                        pₒ pₕ; id] (λ (a b c: D₂.obj) (f : a ⟶ b) (g : b ⟶ c), f ≫ g))                                   

@[hott]
def flat_comp_eq_eta {D₁ D₂ : strict_category} (feq : flat_comp_eq D₁ D₂) :
  feq = flat_comp_eq.mk feq.pₒ feq.pₕ feq.pᵢ feq.pc :=
begin hinduction feq, hsimp end 

@[hott]
def flat_comp_eq_eq {D₁ D₂ : strict_category} (feq₁ feq₂ : flat_comp_eq D₁ D₂) :
  Π (qₒ : feq₁.pₒ = feq₂.pₒ), (feq₁.pₕ =[qₒ; λ q : D₁.obj = D₂.obj, (λ a b : D₁.obj, 
    (a ⟶ b)) =[q; λ D : Set, D -> D -> Set] λ a b : D₂.obj, (a ⟶ b)] feq₂.pₕ) -> 
    feq₁ = feq₂ :=
begin
  intros qₒ qₕ, rwr flat_comp_eq_eta feq₁, rwr flat_comp_eq_eta feq₂, 
  fapply apd01111_v2 flat_comp_eq.mk, 
  { exact qₒ },
  { exact qₕ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end   

@[hott]
def eq_to_flat_comp_eq  {D₁ D₂ : strict_category} : 
  D₁ = D₂ -> flat_comp_eq D₁ D₂ :=
begin 
  intro p, fapply flat_comp_eq.mk,  
  { exact ap strict_category.obj p },
  { sorry },
  { sorry },
  { sorry }, 
end  

@[hott]
structure comp_eq (D₁ D₂ : strict_category) :=
  (Pₒ : D₁.obj = D₂.obj)  
  (Pₕ : Π a b : D₁.obj, (a ⟶ b) = (Pₒ ▸[λ D : Set, D.carrier] a ⟶ Pₒ ▸ b))
  (id_eq : Π a : D₁.obj, (Pₕ a a) ▸ 𝟙 a = 𝟙 (Pₒ ▸[λ D : Set, D.carrier] a))
  (comp_hom_eq : Π (a b c : D₁.obj) (f : a ⟶ b) (g : b ⟶ c), (Pₕ a c) ▸ (f ≫ g) = 
                            ((Pₕ a b) ▸ f) ≫ ((Pₕ b c) ▸ g))                                               

@[hott]
def comp_eq_eta {D₁ D₂ : strict_category} (eq : comp_eq D₁ D₂) :
  eq = comp_eq.mk eq.Pₒ eq.Pₕ eq.id_eq eq.comp_hom_eq :=
begin hinduction eq, hsimp end   

@[hott]
def eq_of_comp_eq {D₁ D₂ : strict_category} (ceq₁ ceq₂ : comp_eq D₁ D₂) :
  Π (pₒ : ceq₁.Pₒ = ceq₂.Pₒ), (ceq₁.Pₕ =[pₒ; λ P : D₁.obj = D₂.obj, Π a b : D₁.obj, 
    (a ⟶ b) = (P ▸[λ D : Set, D.carrier] a ⟶ P ▸ b)] ceq₂.Pₕ) -> ceq₁ = ceq₂ :=
begin
  intros pₒ pₕ, rwr comp_eq_eta ceq₁, rwr comp_eq_eta ceq₂, 
  fapply apd01111_v2 comp_eq.mk, 
  { exact pₒ },
  { exact pₕ },
  { apply pathover_of_tr_eq, apply eq_of_homotopy, intro a, exact is_set.elim _ _ },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b c, 
                             apply eq_of_homotopy2, intros f g, exact is_set.elim _ _ }
end   

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
def eq_to_obj_eq {D₁ D₂ : strict_category} : Π (p : D₁ = D₂), D₁.obj = D₂.obj :=
  assume p, ap (λ D : strict_category, D.obj) p

@[hott, hsimp]
def eq_to_obj_eq_idp (D : strict_category) : eq_to_obj_eq (@idp _ D) = @idp _ D.obj :=
  ap_idp _ _

@[hott, hsimp]
def eq_to_hom_eq {D₁ D₂ : strict_category} : 
  Π (p : D₁ = D₂) (a b : D₁.obj), (a ⟶ b) = (eq_to_obj_eq p ▸[λ D : Set, D.carrier] a ⟶ 
                                              eq_to_obj_eq p ▸ b) :=
begin 
  intro p, --apply fn2_eval_eq_to_deq, exact apd (λ D : Set, @has_hom.hom D _) (eq_to_obj_eq p)
  hsimp, let H := apo100 p (apd (λ D, @has_hom.hom ↥(D.obj) _) p), exact H 
end   

@[hott, hsimp]
def eq_to_hom_eq_idp {D : strict_category} (a b : D.obj) : 
  eq_to_hom_eq (@idp _ D) a b = @idp _ (a ⟶ b) :=
begin hsimp, rwr cast_def end 

@[hott, hsimp]
def eq_to_comp_eq (D₁ D₂ : strict_category) : D₁ = D₂ -> comp_eq D₁ D₂ :=
begin
  intro p, fapply comp_eq.mk, 
  { exact eq_to_obj_eq p },
  { intros a b, exact eq_to_hom_eq p a b },
  { intro a, hinduction p, hsimp },
  { intros a b c f g, induction p, hsimp }
end    

@[hott]
def comp_eq_to_eq (D₁ D₂ : strict_category) : 
  comp_eq D₁ D₂ -> D₁ = D₂ :=
begin
  intro comp_eq, hinduction comp_eq with Pₒ Pₕ id_eq comp_eq,
  apply (λ q, concat q (flat_eta D₂)⁻¹), apply concat (flat_eta D₁),  
  fapply apd01d6 flat_mk,  
  { exact Pₒ },
  { exact fn2_deq_to_eval_eq Pₒ Pₕ },
  { hinduction D₁ with obj₁ precat₁, hinduction D₂ with obj₂ precat₂,
    change obj₁ = obj₂ at Pₒ, hinduction Pₒ, hsimp,
    apply @fn2_po_adp011_idp_eq _ _ (λ (A : Set) (b : A → A → Set), Π (a : A), b a a) 
                                    _ _ _ (eq_of_homotopy2 Pₕ), 
    apply fn2_po_of_tr_eq (eq_of_homotopy2 Pₕ), rwr ap100_eq_of_hty2_inv, exact id_eq },
  { hinduction D₁ with obj₁ precat₁, hinduction D₂ with obj₂ precat₂,
    change obj₁ = obj₂ at Pₒ, hinduction Pₒ, hsimp,
    apply @fn2_po_adp011_idp_eq _ _ (λ (A : Set) (H : A → A → Set), 
             Π {a b c : A}, (H a b) → (H b c) → (H a c)) _ _ _ (eq_of_homotopy2 Pₕ), 
    apply fn2_po_of_tr_eq' (eq_of_homotopy2 Pₕ), rwr ap100_eq_of_hty2_inv, exact comp_eq },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b f, exact is_set.elim _ _ },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b f, exact is_set.elim _ _ },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b c, 
      apply eq_of_homotopy3, intros d f g, apply eq_of_homotopy, intro h, 
      exact is_set.elim _ _ }
end

@[hott]
def comp_eq_to_eq_obj {D₁ D₂ : strict_category} (ceq : comp_eq D₁ D₂) :
  (eq_to_comp_eq D₁ D₂ (comp_eq_to_eq D₁ D₂ ceq)).Pₒ = ceq.Pₒ :=
begin 
  hinduction ceq, 
  change ap (λ D : strict_category, D.obj) ((flat_eta D₁) ⬝ 
                              (apd01d6 flat_mk _ _ _ _ _ _ _) ⬝ (flat_eta D₂)⁻¹) = Pₒ,
  rwr ap_con, rwr ap_con, rwr ap_inv, 
  rwr ap_obj_flat_eta, rwr ap_obj_flat_eta, 
  rwr idp_inv, rwr idp_con, rwr con_idp, 
  let H' : Π o h i c ic ci as, strict_category.obj (flat_mk o h i c ic ci as) = o := 
    begin assume o h i c ic ci as, exact idp end,
  rwr ap_apd01d6 _ _ _ _ _ _ _ _ _ H', rwr idp_con
end  

@[hott]
def comp_eq_to_eq_hom {D₁ D₂ : strict_category} (ceq : comp_eq D₁ D₂) :
  (eq_to_comp_eq D₁ D₂ (comp_eq_to_eq D₁ D₂ ceq)).Pₕ =[comp_eq_to_eq_obj ceq; 
          λ (P : D₁.obj = D₂.obj), Π (a b : D₁.obj), (a ⟶ b) = (P ▸ a ⟶ P ▸ b)] ceq.Pₕ :=
begin
  apply pathover_of_tr_eq, apply eq_of_homotopy2, intros a b, 
  hinduction ceq, change _ = Pₕ a b,
  hinduction D₁ with obj₁ precat₁, hinduction D₂ with obj₂ precat₂, 
  change obj₁ = obj₂ at Pₒ, hinduction Pₒ, change ↥obj₁ at a, change ↥obj₁ at b, 
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
    hsimp, change apd01111' (@precategory.mk _) _ _ _ _ = 
                                            apd01111' (@precategory.mk _) idp idpo idpo idpo,
    fapply apd01111' (apd01111' (@precategory.mk _)), 
    { hinduction cat_struct with has_hom id comp, hinduction has_hom with hom, hsimp, 
      change apd0111' (@category_struct.mk _) _ _ _ = 
                                               apd0111' (@category_struct.mk _) idp idpo idpo,
      fapply apd0111' (apd0111' (@category_struct.mk _)), 
      { change _ = ap has_hom.mk idp, apply ap (ap has_hom.mk), 
        change eq_of_homotopy2 (λ (a b : ↥obj), idp) = _, rwr eq_of_homotopy2_id },
      { apply pathover_of_tr_eq, apply dep_set_eq_eq _ _ _, apply is_set_dmap' },
      { apply pathover_of_tr_eq, apply dep_set_eq_eq _ _ _, apply is_set_dmap' } },
    { apply pathover_of_tr_eq, apply dep_set_eq_eq _ _ _, apply is_set_dmap' },
    { apply pathover_of_tr_eq, apply dep_set_eq_eq _ _ _, apply is_set_dmap' },
    { apply pathover_of_tr_eq, apply dep_set_eq_eq _ _ _, apply is_set_dmap' } }
end  

@[hott]
def eq_eqv_comp_eq (D₁ D₂ : strict_category) : D₁ = D₂ ≃ comp_eq D₁ D₂ :=
begin
  fapply equiv.mk, 
  { exact eq_to_comp_eq D₁ D₂ },
  { fapply adjointify, 
    { exact comp_eq_to_eq D₁ D₂ },
    { intro b, fapply eq_of_comp_eq, 
      { exact comp_eq_to_eq_obj b },
      { exact comp_eq_to_eq_hom b } },
    { intro p, hinduction p, exact comp_eq_to_eq_idp D₁ } }
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

end categories

end hott