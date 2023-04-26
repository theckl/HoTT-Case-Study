import sets.algebra init2 sets.axioms sets.theories categories.basic categories.adjoints

universes v v' u u' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc hott.is_equiv 
     hott.equiv hott.precategories hott.categories
     hott.categories.adjoints 

namespace categories

namespace strict

/- Precategories whose type of objects is a set are called `strict categories` following 
   the [HoTT-Book,Ch.9.6], but they do not need to be categories. Thus we allow diagrams 
   with loops, that is cycles of homomorphisms that always yield the identity 
   homomorphism when composed. 
  
   Strict categories together with functors between them form a precategory in a 
   straightforward way. The strictness is needed to show that homomorphisms =
   functors are sets. -/
@[hott]
class is_strict (C : Precategory) :=
  (set : is_set C)

attribute [instance] is_strict.set

@[hott, instance] 
def is_strict_is_prop (C : Precategory) : is_prop (is_strict C) :=
begin
  fapply is_prop.mk, intros s₁ s₂, 
  hinduction s₁ with s₁, hinduction s₂ with s₂, 
  fapply ap is_strict.mk, exact is_prop.elim _ _
end

@[hott, instance]
def functors_of_strict_cat_is_set (D₁ D₂ : Precategory) 
  [is_strict D₁] [HD₂ : is_strict D₂]: is_set (D₁ ⥤ D₂) :=
begin 
  apply is_trunc_equiv_closed_rev 0 (functor_eqv_sig D₁ D₂),
  fapply dprod_of_Sets_is_set' _ _,
  { apply is_trunc_equiv_closed_rev 0 (functor_ops_eqv_sig D₁ D₂),
    fapply dprod_of_Sets_is_set' _ _,
    { apply_instance },
    { intro map, apply_instance } },
  { intro map, apply_instance }
end    

@[hott]
structure strict_Category :=
  (Precat : Precategory)
  (strict : is_strict Precat)

@[hott] instance : has_coe_to_sort strict_Category := 
  has_coe_to_sort.mk Type.{u} (λ D, D.Precat.obj)

attribute [instance] strict_Category.strict

@[hott]
def strict_cat_sig := Σ (C : Precategory), is_strict C

@[hott]
def strict_cat_eqv_sig : strict_Category ≃ strict_cat_sig :=
begin
  fapply equiv.mk,
  { intro C, exact ⟨C.Precat, C.strict⟩ },
  { fapply adjointify,
    { intro C_sig, exact strict_Category.mk C_sig.1 C_sig.2 },
    { intro C_sig, hsimp, hinduction C_sig, hsimp },
    { intro C, hinduction C, hsimp } }
end

@[hott]
def strict_cat_sig_eq_eqv_precat_eq (D₁ D₂ : strict_cat_sig) :
  (D₁ = D₂) ≃ (D₁.1 = D₂.1) :=
sigma.subtype_eq_equiv _ _ 

@[hott]
def strict_cat_eq_eqv_precat_eq (D₁ D₂ : strict_Category) :
  (D₁ = D₂) ≃ (D₁.Precat = D₂.Precat) :=
eq_equiv_fn_eq_of_equiv strict_cat_eqv_sig _ _ ⬝e
strict_cat_sig_eq_eqv_precat_eq _ _

@[hott, instance]
def strict_cat_has_hom : has_hom (strict_Category) :=
  has_hom.mk (λ D₁ D₂ : strict_Category, Set.mk (D₁ ⥤ D₂) 
               (functors_of_strict_cat_is_set D₁.Precat D₂.Precat))     

@[hott, instance]
def strict_cat_cat_str : category_struct strict_Category :=
  category_struct.mk (λ D, id_functor D) (λ D₁ D₂ D₃ F G, F ⋙ G)

@[hott, instance]
def strict_cat_precat : is_precat strict_Category :=
is_precat.mk (λ D₁ D₂ F, funct_id_comp F) 
               (λ D₁ D₂ F, funct_comp_id F) 
               (λ D₁ D₂ D₃ D₄ F G H, funct_comp_assoc F G H)

/- It is more complicated to show that the precategory of strict categories is actually a 
   category. To construct an equivalence between the identity type of two strict 
   categories and the type of isomorphism between them as given by the category structure, 
   we use one of the three types of equivalences between (pre)categories discussed in the 
   [HoTT-Book, Sec.9.4] as an intermediate step: In [Def.9.4.8], they are also called 
   isomorphisms of (pre)categories.
   
   The equivalence between equalities and these isomorphisms is constructed in 
   [Lem.9.4.15] without the strictness assumption; this is `precat_id_equiv_iso`
   in [categories.precat]. We reformulate it for strict categories. -/
@[hott]
def strict_cat_iso (C D : strict_Category) := 
  precat_iso C.Precat D.Precat

@[hott, reducible]
def strict_cat_eq_equiv_iso (C D : strict_Category) : 
  (C = D) ≃ (strict_cat_iso C D) :=  
strict_cat_eq_eqv_precat_eq C D ⬝e precat_id_equiv_iso _ _

@[hott]
def strict_cat_iso.inv {C D : strict_Category} :
  strict_cat_iso C D -> D ⥤ C :=
begin
  intro sc_iso, hinduction sc_iso with funct ff equiv,
  let obj_inv := @is_equiv.inv _ _ _ equiv,
  fapply precategories.functor.mk,
  { exact λ d, obj_inv d },
  { intros x y g, 
    apply (inv_bijection_of (is_fully_faithful_functor' @ff 
                   (obj_inv x) (obj_inv y))).map, 
    exact (idtoiso (@is_equiv.right_inv _ _ _ equiv x)).hom ≫ g 
          ≫ (idtoiso (@is_equiv.right_inv _ _ _ equiv y)).ih.inv },
  { intro x, apply hott.eq.inverse, apply bijection_l_to_r, 
    change funct.map _ = _, rwr funct.map_id, 
    apply concat _ (ap (λ h : x ⟶ funct.obj (obj_inv x), 
           (idtoiso (@is_equiv.right_inv _ _ _ equiv x)).hom ≫ h) 
           (hott.eq.inverse (@is_precat.id_comp _ D.Precat.struct x _ _))),
    hsimp, rwr is_iso.l_inv },
  { intros x y z f g, apply hott.eq.inverse, apply bijection_l_to_r,
    change funct.map _ = _, rwr funct.map_comp,  
    let hxy := is_fully_faithful_functor' @ff (obj_inv x) (obj_inv y),
    let hyz := is_fully_faithful_functor' @ff (obj_inv y) (obj_inv z),
    change (hxy ((inv_bijection_of hxy) _)) ≫ 
               (hyz ((inv_bijection_of hyz) _)) = _,
    rwr inv_bij_r_inv, rwr inv_bij_r_inv, 
    let as := @is_precat.assoc _ D.Precat.struct,
    rwr <- as _ g _, 
    rwr as (idtoiso (@is_equiv.right_inv _ _ _ equiv x)).hom _ _, 
    rwr as f _ _, 
    rwr <- as (idtoiso (@is_equiv.right_inv _ _ _ equiv y)).ih.inv _ _,
    rwr <- as _ _ g, rwr is_iso.r_inv, 
    rwr @is_precat.id_comp _ D.Precat.struct y _ _, rwr <- as f _ _ }
end

@[hott]
def strict_cat_iso_inv_left {C D : strict_Category} :
  Π (sc_iso : strict_cat_iso C D), 
    @category_struct.comp strict_Category _ _ _ _ 
             (strict_cat_iso.inv sc_iso) sc_iso.functor = 𝟙 D :=
begin 
  intro sc_iso, fapply functor_eq', 
  { intro x, hinduction sc_iso with funct ff equiv,
    exact @is_equiv.right_inv _ _ _ equiv x },
  { intros x y g,  
    change _ ≫ sc_iso.functor.map (sc_iso.inv.map g) ≫ _ = g, 
    hinduction sc_iso with funct ff equiv,
    let obj_inv := @is_equiv.inv _ _ _ equiv,
    change _ ≫ ((is_fully_faithful_functor' @ff (obj_inv x)
                      (obj_inv y))) ((inv_bijection_of 
                  (is_fully_faithful_functor' @ff (obj_inv x)
                    (obj_inv y))) (_ ≫ g ≫ _)) ≫ _ = _,
    rwr inv_bij_r_inv (is_fully_faithful_functor' @ff (obj_inv x)
                         (obj_inv y)),          
    rwr <- is_precat.assoc, rwr <- is_precat.assoc _ g _, 
    rwr <- is_precat.assoc _ (_ ≫ g) _, 
    rwr <- is_precat.assoc _ _ g, rwr id_inv_iso_inv,
    change ((((idtoiso _).ih.inv ≫ _) ≫ g) ≫ _) ≫ _  = _,
    rwr is_iso.r_inv, rwr is_precat.id_comp, rwr is_precat.assoc,
    rwr is_iso.r_inv, rwr is_precat.comp_id }
end             

@[hott]
def strict_cat_iso_inv_right {C D : strict_Category} :
  Π (sc_iso : strict_cat_iso C D), 
    @category_struct.comp strict_Category _ _ _ _ 
             sc_iso.functor (strict_cat_iso.inv sc_iso) = 𝟙 C :=
begin
  intro sc_iso, fapply functor_eq', 
  { intro x, hinduction sc_iso with funct ff equiv,
    exact @is_equiv.left_inv _ _ _ equiv x },
  { intros x y f, 
    change _ ≫ sc_iso.inv.map (sc_iso.functor.map f) ≫ _ = f,
    hinduction sc_iso with funct ff equiv, 
    let obj_inv := @is_equiv.inv _ _ _ equiv,
    let obj_linv := @is_equiv.left_inv _ _ _ equiv,
    let obj_rinv := @is_equiv.right_inv _ _ _ equiv,
    change _ ≫ (inv_bijection_of (is_fully_faithful_functor' @ff 
                  (obj_inv (funct.obj x)) (obj_inv (funct.obj y))) 
                  (_ ≫ funct.map f ≫ _)) ≫ _ = _,
    have p : funct.map (idtoiso (obj_linv x)).hom = 
                       (idtoiso (obj_rinv (funct.obj x))).hom, from 
    begin 
      rwr funct_idtoiso, exact ap (iso.hom ∘ idtoiso) (is_set.elim _ _) 
    end,
    have q : funct.map (idtoiso (obj_linv y)).ih.inv = 
                    (idtoiso (obj_rinv (funct.obj y))).ih.inv, from 
    begin 
      change funct.map (idtoiso (obj_linv y))⁻¹ʰ.hom = 
             (idtoiso (obj_rinv (funct.obj y)))⁻¹ʰ.hom, 
      rwr <- id_inv_iso_inv, rwr funct_idtoiso, rwr <- id_inv_iso_inv,
      exact ap (iso.hom ∘ idtoiso) (is_set.elim _ _) 
    end,  
    rwr <- p, rwr <- q, rwr <- functor.map_comp, rwr <- functor.map_comp,
    change _ ≫ (inv_bijection_of (is_fully_faithful_functor' @ff 
                  (obj_inv (funct.obj x)) (obj_inv (funct.obj y)))) 
      (is_fully_faithful_functor' @ff 
       (obj_inv (funct.obj x)) (obj_inv (funct.obj y)) _) ≫ _ = _,
    rwr inv_bij_l_inv, rwr <- is_precat.assoc, rwr <- is_precat.assoc,
    rwr id_inv_iso_inv, 
    change (((idtoiso (obj_linv x)).ih.inv ≫_) ≫ _ ≫ _) ≫_ = _,  
    rwr is_iso.r_inv, rwr is_precat.id_comp, rwr is_precat.assoc,
    rwr is_iso.r_inv, rwr is_precat.comp_id }
end

@[hott, reducible]
def strict_cat_iso_to_iso (C D : strict_Category) :
  strict_cat_iso C D -> C ≅ D :=
begin
  intro sc_iso, fapply iso.mk, 
  { exact sc_iso.functor }, 
  { fapply is_iso.mk,
    { exact strict_cat_iso.inv sc_iso },
    { exact strict_cat_iso_inv_left sc_iso },
    { exact strict_cat_iso_inv_right sc_iso } }
end

@[hott, reducible]
def iso_to_strict_cat_iso (C D : strict_Category) :
  C ≅ D -> strict_cat_iso C D :=
begin 
  intro i, hinduction i with hom is_iso, 
  induction is_iso with inv l_inv r_inv, 
  fapply precat_iso.mk, 
  { exact hom },
  { intros x y, fapply has_inverse_to_is_bijective, 
    { intro g, 
      exact (idtoiso (ap10 (ap functor.obj r_inv) x)⁻¹).hom ≫ 
        @precategories.functor.map _ _ _ _ inv (hom.obj x) 
                                                 (hom.obj y) g ≫
        (idtoiso (ap10 (ap functor.obj r_inv) y)).hom },
    { fapply is_set_inverse_of.mk, 
      { intro g, rwr functor.map_comp, rwr functor.map_comp,
        change _ ≫ (inv ≫ hom).map _ ≫ _ = _, 
        rwr functor_map_eq l_inv⁻¹ g, rwr funct_idtoiso, 
        rwr ap_inv, rwr is_precat.assoc, rwr is_precat.assoc, 
        rwr <- is_precat.assoc, rwr idtoiso_comp_eq,
        rwr funct_idtoiso, rwr idtoiso_comp_eq, 
        change (iso.hom ∘ idtoiso) _  ≫ g ≫ (iso.hom ∘ idtoiso) _ = _, 
        rwr ap (iso.hom ∘ idtoiso) 
                        (@is_set.elim _ D.strict.set _ _ _ idp),
        rwr ap (iso.hom ∘ idtoiso) 
                (@is_set.elim _ D.strict.set _ _ _ (idpath (hom.obj y))),
        change iso.hom (idtoiso idp)  ≫ g ≫ iso.hom (idtoiso idp) = _,
        hsimp },
      { intro g, change _ ≫ (hom ≫ inv).map _ ≫ _ = _, 
        rwr functor_map_eq r_inv⁻¹ g, 
        rwr is_precat.assoc, rwr is_precat.assoc, 
        rwr <- is_precat.assoc, rwr idtoiso_comp_eq,
        rwr idtoiso_comp_eq, 
        change (iso.hom ∘ idtoiso) _  ≫ g ≫ (iso.hom ∘ idtoiso) _ = _, 
        rwr ap (iso.hom ∘ idtoiso) 
                        (@is_set.elim _ C.strict.set _ _ _ idp),
        rwr ap (iso.hom ∘ idtoiso) 
                (@is_set.elim _ C.strict.set _ _ _ (idpath y)),
        change iso.hom (idtoiso idp)  ≫ g ≫ iso.hom (idtoiso idp) = _,
        hsimp } } },
  { fapply adjointify,
    { exact inv.obj },
    { intro x, exact ap10 (ap functor.obj l_inv) x },
    { intro x, exact ap10 (ap functor.obj r_inv) x } }
end

@[hott]
def strict_cat_iso_eqv_iso (C D : strict_Category) :
  (strict_cat_iso C D) ≃ (C ≅ D) :=
begin
  fapply equiv.mk,
  { exact strict_cat_iso_to_iso C D },
  { fapply adjointify,
    { exact iso_to_strict_cat_iso C D },
    { intro i, apply hom_eq_to_iso_eq, fapply functor_eq',
      { intro x, hinduction i with hom is_iso, hinduction is_iso,
        hsimp },
      { intros x y f, hinduction i with hom is_iso, hinduction is_iso,
        change (iso.hom ∘ idtoiso) _ ≫ hom.map f ≫ 
                                    (iso.hom ∘ idtoiso) _ = hom.map f, 
        rwr ap (iso.hom ∘ idtoiso) 
                        (@is_set.elim _ D.strict.set _ _ _ idp),
        rwr ap (iso.hom ∘ idtoiso) (@is_set.elim _ D.strict.set 
                                    _ _ _ (idpath (hom.obj y))),
        change iso.hom (idtoiso idp) ≫ hom.map f ≫ 
                                      iso.hom (idtoiso idp) = _,
        hsimp } },
    { intro sc_iso, apply precat_iso_eq_of_funct_eq, fapply functor_eq',
      { intro x, hinduction sc_iso, hsimp },
      { intros x y f, 
        change (iso.hom ∘ idtoiso) _ ≫ sc_iso.functor.map f ≫ 
                                      (iso.hom ∘ idtoiso) _ = _,
        rwr ap (iso.hom ∘ idtoiso) 
                        (@is_set.elim _ D.strict.set _ _ _ idp),
        rwr ap (iso.hom ∘ idtoiso) (@is_set.elim _ D.strict.set 
                        _ _ _ (idpath (sc_iso.functor.obj y))),
        change iso.hom (idtoiso idp) ≫ sc_iso.functor.map f ≫ 
                                      iso.hom (idtoiso idp) = _,
        hsimp } } }
end

@[hott]
def strict_cat_eq_eqv_iso {C D : strict_Category} :
  (C = D) ≃ (C ≅ D) :=
strict_cat_eq_equiv_iso _ _ ⬝e strict_cat_iso_eqv_iso _ _ 

@[hott]
def idtoiso_strictcattoiso (C D : strict_Category) :
  Π (p : C = D), idtoiso p = (strict_cat_eq_eqv_iso).to_fun p :=
begin 
  intro p, change _ = ((_ ⬝e _) ⬝e _).to_fun p, 
  rwr equiv.to_fun_trans, 
  change _ = (strict_cat_iso_eqv_iso C D).to_fun 
                                            ((_ ⬝e _).to_fun p),
  rwr equiv.to_fun_trans, hinduction p,
  rwr idtoiso_refl_eq, 
  change _ = (strict_cat_iso_eqv_iso C C).to_fun
             ((precat_iso_of_obj_equiv_iso C.Precat C.Precat).to_fun
              ((_ ⬝e _).to_fun idp)),
  rwr equiv.to_fun_trans, 
  change _ = (strict_cat_iso_eqv_iso C C).to_fun
      ((precat_iso_of_obj_equiv_iso C.Precat C.Precat).to_fun
         ((precat_sig_equiv_obj_iso C.Precat C.Precat).to_fun idp)),
  apply hom_eq_to_iso_eq,
  change 𝟙 C = ((precat_iso_of_obj_equiv_iso C.Precat C.Precat).to_fun
          ((precat_sig_equiv_obj_iso C.Precat C.Precat).to_fun idp)).functor, 
  fapply functor_eq',
  { intro x, hsimp,
    have r : ((precat_sig_equiv_obj_iso C.Precat C.Precat).to_fun 
             (refl ⟨C.Precat.obj, C.Precat.struct⟩)).fst = @equiv.rfl C,
    from precat_sig_equiv_obj_iso_idp C.Precat C.Precat, 
    rwr r },
  { intros x y f,
    change (iso.hom ∘ idtoiso) _ ≫ f ≫ (iso.hom ∘ idtoiso) _ = _, 
    rwr ap (iso.hom ∘ idtoiso) 
                        (@is_set.elim _ C.strict.set _ _ _ idp),
    rwr ap (iso.hom ∘ idtoiso) 
                 (@is_set.elim _ C.strict.set _ _ _ (idpath y)),                    
    change iso.hom (idtoiso idp) ≫ f ≫ iso.hom (idtoiso idp) = _,
    hsimp, 
    change _ = ((precat_sig_equiv_obj_iso C.Precat C.Precat).to_fun idp).snd.hom_map f,
    have r : ((precat_sig_equiv_obj_iso C.Precat C.Precat).to_fun idp).snd.hom_map =
             (id_functor C).map, from 
      precat_sig_equiv_obj_iso_idp_map C.Precat C.Precat, 
    rwr r } 
end

end strict

open strict

@[hott, instance]
def strict_cat_is_cat : is_cat strict_Category :=
begin
  apply is_cat.mk, intros D₁ D₂, change is_equiv (λ p, idtoiso p), 
  rwr eq_of_homotopy (idtoiso_strictcattoiso D₁ D₂),
  apply_instance
end                 

@[hott]
def Category_of_strict_Categories : Category :=
  Category.mk strict_Category strict_cat_is_cat

end categories

end hott