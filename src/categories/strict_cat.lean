import categories.adjoints 

universes v v' u u' w 
hott_theory

namespace hott
open hott.set hott.is_trunc hott.precategories

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
class is_strict_cat (obj : Type u) extends is_precat.{v} obj :=
  (set : is_set obj)

attribute [instance] is_strict_cat.to_is_precat
attribute [instance] is_strict_cat.set

@[hott, instance]
def functors_of_strict_cat_is_set (D₁ D₂ : Type _) 
  [is_strict_cat D₁] [HD₂ : is_strict_cat D₂] : is_set (D₁ ⥤ D₂) :=
begin 
  apply is_trunc_equiv_closed_rev 0 (functor_eqv_sig D₁ D₂),
  fapply dprod_of_Sets_is_set' _ _,
  { apply is_trunc_equiv_closed_rev 0 (functor_ops_eqv_sig D₁ D₂), 
    fapply dprod_of_Sets_is_set' _ _, 
    { apply_instance }, 
    { intro map, apply_instance } },
  { apply_instance }
end  

@[hott]
structure strict_Category :=
  (obj : Type _)
  (strict_cat : is_strict_cat obj)

@[hott] instance : has_coe_to_sort strict_Category := 
  has_coe_to_sort.mk Type.{u} (λ D, D.obj)

@[hott, instance]
def strict_Category_is_precat : Π (D : strict_Category), is_precat D.obj :=
  λ D, @is_strict_cat.to_is_precat D D.strict_cat

@[hott] 
def strict_Cat.to_Precat : strict_Category -> Precategory :=
  λ C, Precategory.mk C.obj (@is_strict_cat.to_is_precat C.obj C.strict_cat)

@[hott]
def strict_cat_sig := Σ (pc_sig : Precat_sig), is_set pc_sig.1

@[hott]
def strict_cat_eqv_sig : strict_Category ≃ strict_cat_sig :=
begin
  fapply equiv.mk,
  { intro C, exact ⟨⟨C, @is_strict_cat.to_is_precat C.obj C.strict_cat⟩, C.strict_cat.set⟩ },
  { fapply is_equiv.adjointify,
    { intro C_sig, exact strict_Category.mk C_sig.1.1 
                        (@is_strict_cat.mk C_sig.1.1 C_sig.1.2 C_sig.2) },
    { intro C_sig, hsimp, hinduction C_sig, hsimp, hinduction fst, refl },
    { intro C, hinduction C, hsimp, hinduction strict_cat, refl } }
end

@[hott]
def strict_cat_sig_eq_eqv_pc_sig_eq (D₁ D₂ : strict_cat_sig) :
  (D₁ = D₂) ≃ (D₁.1 = D₂.1) :=
sigma.subtype_eq_equiv _ _ 

@[hott]
def strict_cat_eq_eqv_precat_eq (D₁ D₂ : strict_Category) :
  (D₁ = D₂) ≃ (strict_Cat.to_Precat D₁ = strict_Cat.to_Precat D₂) :=
equiv.eq_equiv_fn_eq_of_equiv strict_cat_eqv_sig _ _ ⬝e
strict_cat_sig_eq_eqv_pc_sig_eq _ _ ⬝e
(equiv.eq_equiv_fn_eq_of_equiv Precat_str_equiv_sig _ _)⁻¹ᵉ 

@[hott]
def strict_cat_idp_to_precat_idp (D : strict_Category) :
  (strict_cat_eq_eqv_precat_eq D D).to_fun idp = idp :=
begin change (_ ⬝e _ ⬝e _).to_fun _ = _, rwr equiv.to_fun_trans end

@[hott, instance]
def strict_cat_has_hom : has_hom (strict_Category) :=
  has_hom.mk (λ D₁ D₂ : strict_Category, Set.mk (@precategories.functor D₁ (D₁.strict_cat.to_is_precat) 
                                                                        D₂ (D₂.strict_cat.to_is_precat)) 
                (@functors_of_strict_cat_is_set D₁ D₂ D₁.strict_cat D₂.strict_cat))     

@[hott, instance]
def strict_cat_cat_str : category_struct strict_Category :=
  category_struct.mk (λ D, @id_functor D (D.strict_cat.to_is_precat)) 
                     (λ D₁ D₂ D₃ F G, @precategories.functor_comp D₁ (D₁.strict_cat.to_is_precat) 
                                       D₂ (D₂.strict_cat.to_is_precat) D₃ (D₃.strict_cat.to_is_precat) F G)

@[hott, instance]
def strict_cat_precat : is_precat strict_Category :=
is_precat.mk (λ D₁ D₂ F, @funct_id_comp  D₁ (D₁.strict_cat.to_is_precat) D₂ (D₂.strict_cat.to_is_precat) F) 
               (λ D₁ D₂ F, @funct_comp_id D₁ (D₁.strict_cat.to_is_precat) D₂ (D₂.strict_cat.to_is_precat) F) 
               (λ D₁ D₂ D₃ D₄ F G H, @funct_comp_assoc D₁ (D₁.strict_cat.to_is_precat) 
                                       D₂ (D₂.strict_cat.to_is_precat) D₃ (D₃.strict_cat.to_is_precat)
                                       D₄ (D₄.strict_cat.to_is_precat) F G H)

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
def strict_cat_iso (C D : Type _) [sc : is_strict_cat C] [sd : is_strict_cat D] := 
  @precat_iso C D sc.to_is_precat sd.to_is_precat

@[hott]
def strict_cat_iso.hom {C D : Type _} [sc : is_strict_cat C] [sd : is_strict_cat D] :
  strict_cat_iso C D -> (strict_Category.mk C sc ⟶ strict_Category.mk D sd) :=
λ sc_iso, sc_iso.functor  

@[hott, reducible]
def strict_cat_eq_equiv_iso (C D : Type _) [is_strict_cat C] [is_strict_cat D] : 
  ((strict_Category.mk C _) = (strict_Category.mk D _)) ≃ (strict_cat_iso C D) :=  
strict_cat_eq_eqv_precat_eq (strict_Category.mk C _) (strict_Category.mk D _) ⬝e Precat_id_equiv_iso _ _

@[hott]
def strict_cat_iso.inv {C D : Type _} [sc : is_strict_cat C] [sd : is_strict_cat D] :
  strict_cat_iso C D -> (strict_Category.mk D sd ⟶ strict_Category.mk C sc) :=
begin
  intro sc_iso, hinduction sc_iso with funct ff equiv,
  let obj_inv := @is_equiv.inv _ _ _ equiv,
  fapply precategories.functor.mk,
  { exact λ d, obj_inv d },
  { intros x y g, 
    apply (inv_bijection_of (is_fully_faithful_functor' @ff (obj_inv x) (obj_inv y))).map, 
    exact (idtoiso (@is_equiv.right_inv _ _ _ equiv x)).hom ≫ g 
          ≫ (idtoiso (@is_equiv.right_inv _ _ _ equiv y)).ih.inv },
  { intro x, apply hott.eq.inverse, apply bijection_l_to_r, 
    change funct.map _ = _, rwr funct.map_id, 
    apply concat _ (ap (λ h : x ⟶ funct.obj (obj_inv x), 
           (idtoiso (@is_equiv.right_inv _ _ _ equiv x)).hom ≫ h) 
           (hott.eq.inverse (@is_precat.id_comp _ 
                             (is_strict_cat.to_is_precat D) x _ _))),
    hsimp, rwr is_iso.l_inv },
  { intros x y z f g, apply hott.eq.inverse, apply bijection_l_to_r,
    change funct.map _ = _, rwr funct.map_comp,  
    let hxy := is_fully_faithful_functor' @ff (obj_inv x) (obj_inv y),
    let hyz := is_fully_faithful_functor' @ff (obj_inv y) (obj_inv z),
    change (hxy.map ((inv_bijection_of hxy).map _)) ≫ 
               (hyz.map ((inv_bijection_of hyz).map _)) = _,
    rwr inv_bij_r_inv, rwr inv_bij_r_inv, 
    let as := @is_precat.assoc _ (is_strict_cat.to_is_precat D),
    rwr <- as _ g _, 
    rwr as (idtoiso (@is_equiv.right_inv _ _ _ equiv x)).hom _ _, 
    rwr as f _ _, 
    rwr <- as (idtoiso (@is_equiv.right_inv _ _ _ equiv y)).ih.inv _ _,
    rwr <- as _ _ g, rwr is_iso.r_inv, 
    rwr @is_precat.id_comp _ (is_strict_cat.to_is_precat D) y _ _, 
    rwr <- as f _ _ }
end

@[hott]
def strict_cat_iso_inv_left (C D : Type _) [sc : is_strict_cat C] [sd : is_strict_cat D] 
  (sc_iso : strict_cat_iso C D) : 
    (strict_cat_iso.inv sc_iso) ≫ strict_cat_iso.hom sc_iso  = 𝟙 (strict_Category.mk D sd) :=
begin 
  fapply functor_eq', 
  { intro x, hinduction sc_iso with funct ff equiv,
    exact @is_equiv.right_inv _ _ _ equiv x },
  { intros x y g,  
    change _ ≫ sc_iso.functor.map (sc_iso.inv.map g) ≫ _ = g, 
    hinduction sc_iso with funct ff equiv,
    let obj_inv := @is_equiv.inv _ _ _ equiv,
    change _ ≫ (is_fully_faithful_functor' @ff (obj_inv x)
                      (obj_inv y)).map ((inv_bijection_of 
                  (is_fully_faithful_functor' @ff (obj_inv x)
                    (obj_inv y))).map (_ ≫ g ≫ _)) ≫ _ = _,
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
def strict_cat_iso_inv_right (C D : Type _) [sc : is_strict_cat C] [sd : is_strict_cat D] 
  (sc_iso : strict_cat_iso C D) : 
  strict_cat_iso.hom sc_iso ≫ (strict_cat_iso.inv sc_iso) = 𝟙 (strict_Category.mk C sc) :=
begin
  fapply functor_eq', 
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
      rwr funct_idtoiso, exact ap (iso.hom ∘ idtoiso) 
           (@is_set.elim D _ _ _ _ _) 
    end,
    have q : funct.map (idtoiso (obj_linv y)).ih.inv = 
                    (idtoiso (obj_rinv (funct.obj y))).ih.inv, from 
    begin 
      change funct.map (idtoiso (obj_linv y))⁻¹ʰ.hom = 
             (idtoiso (obj_rinv (funct.obj y)))⁻¹ʰ.hom, 
      rwr <- id_inv_iso_inv, rwr funct_idtoiso, rwr <- id_inv_iso_inv,
      exact ap (iso.hom ∘ idtoiso) (@is_set.elim D _ _ _ _ _) 
    end,  
    rwr <- p, rwr <- q, rwr <- functor.map_comp, rwr <- functor.map_comp,
    change _ ≫ (inv_bijection_of (is_fully_faithful_functor' @ff 
                  (obj_inv (funct.obj x)) (obj_inv (funct.obj y)))).map 
      ((is_fully_faithful_functor' @ff 
       (obj_inv (funct.obj x)) (obj_inv (funct.obj y))).map _) ≫ _ = _,
    rwr inv_bij_l_inv, rwr <- is_precat.assoc, rwr <- is_precat.assoc,
    rwr id_inv_iso_inv, 
    change (((idtoiso (obj_linv x)).ih.inv ≫_) ≫ _ ≫ _) ≫_ = _,  
    rwr is_iso.r_inv, rwr is_precat.id_comp, rwr is_precat.assoc,
    rwr is_iso.r_inv, rwr is_precat.comp_id }
end

@[hott, reducible]
def strict_cat_iso_to_iso (C D : strict_Category) :
  @strict_cat_iso C.obj D.obj C.strict_cat D.strict_cat -> C ≅ D :=
begin
  intro sc_iso, fapply iso.mk, 
  { exact @strict_cat_iso.hom _ _ C.strict_cat D.strict_cat sc_iso }, 
  { fapply is_iso.mk,
    { exact @strict_cat_iso.inv _ _ C.strict_cat D.strict_cat sc_iso },
    { exact @strict_cat_iso_inv_left _ _ C.strict_cat D.strict_cat sc_iso },
    { exact @strict_cat_iso_inv_right _ _ C.strict_cat D.strict_cat sc_iso } }
end

@[hott, reducible]
def iso_to_strict_cat_iso (C D : Type _) [sc : is_strict_cat C] [sd : is_strict_cat D] :
  strict_Category.mk C sc ≅ strict_Category.mk D sd -> strict_cat_iso C D :=
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
                        (@is_set.elim D _ _ _ _ idp),
        rwr ap (iso.hom ∘ idtoiso) 
                (@is_set.elim D _ _ _ _ (idpath (hom.obj y))),
        change iso.hom (idtoiso idp)  ≫ g ≫ iso.hom (idtoiso idp) = _,
        hsimp },
      { intro g, change _ ≫ (hom ≫ inv).map _ ≫ _ = _, 
        rwr functor_map_eq r_inv⁻¹ g, 
        rwr is_precat.assoc, rwr is_precat.assoc, 
        rwr <- is_precat.assoc, rwr idtoiso_comp_eq,
        rwr idtoiso_comp_eq, 
        change (iso.hom ∘ idtoiso) _  ≫ g ≫ (iso.hom ∘ idtoiso) _ = _, 
        rwr ap (iso.hom ∘ idtoiso) 
                        (@is_set.elim C _ _ _ _ idp),
        rwr ap (iso.hom ∘ idtoiso) 
                (@is_set.elim C _ _ _ _ (idpath y)),
        change iso.hom (idtoiso idp)  ≫ g ≫ iso.hom (idtoiso idp) = _,
        hsimp } } },
  { fapply is_equiv.adjointify,
    { exact inv.obj },
    { intro x, exact ap10 (ap functor.obj l_inv) x },
    { intro x, exact ap10 (ap functor.obj r_inv) x } }
end

@[hott]
def strict_cat_iso_eqv_iso (C D : Type _) [sc : is_strict_cat C] [sd : is_strict_cat D] :
  (strict_cat_iso C D) ≃ (strict_Category.mk C sc ≅ strict_Category.mk D sd) :=
begin
  fapply equiv.mk,
  { exact strict_cat_iso_to_iso (strict_Category.mk C sc) (strict_Category.mk D sd) },
  { fapply is_equiv.adjointify,
    { exact iso_to_strict_cat_iso C D },
    { intro i, apply hom_eq_to_iso_eq, fapply functor_eq',
      { intro x, hinduction i with hom is_iso, hinduction is_iso, exact idp },
      { intros x y f, hinduction i with hom is_iso, hinduction is_iso,
        change (iso.hom ∘ idtoiso) _ ≫ hom.map f ≫ 
                                    (iso.hom ∘ idtoiso) _ = hom.map f, 
        rwr ap (iso.hom ∘ idtoiso) 
                        (@is_set.elim D _ _ _ _ idp),
        rwr ap (iso.hom ∘ idtoiso) (@is_set.elim D _ 
                                    _ _ _ (idpath (hom.obj y))),
        change iso.hom (idtoiso idp) ≫ hom.map f ≫ 
                                      iso.hom (idtoiso idp) = _,
        hsimp } },
    { intro sc_iso, apply precat_iso_eq_of_funct_eq, fapply functor_eq',
      { intro x, hinduction sc_iso, exact idp },
      { intros x y f, 
        change (iso.hom ∘ idtoiso) _ ≫ sc_iso.functor.map f ≫ 
                                      (iso.hom ∘ idtoiso) _ = _,
        rwr ap (iso.hom ∘ idtoiso) 
                        (@is_set.elim D _ _ _ _ idp),
        rwr ap (iso.hom ∘ idtoiso) (@is_set.elim D _ 
                        _ _ _ (idpath (sc_iso.functor.obj y))),
        change iso.hom (idtoiso idp) ≫ sc_iso.functor.map f ≫ 
                                      iso.hom (idtoiso idp) = _,
        hsimp } } }
end

@[hott]
def strict_cat_eq_eqv_iso (C D : strict_Category) : (C = D) ≃ (C ≅ D) :=
begin 
  hinduction C with C_obj C_str, hinduction D with D_obj D_str, 
  exact @strict_cat_eq_equiv_iso _ _ C_str D_str ⬝e @strict_cat_iso_eqv_iso _ _ C_str D_str
end

@[hott]
def idtoiso_strictcattoiso (C D : strict_Category) :
  Π (p : C = D), idtoiso p = (strict_cat_eq_eqv_iso C D).to_fun p :=
begin 
  intro p, hinduction p, rwr idtoiso_refl_eq, hinduction C with C str, 
  change _ = (@strict_cat_iso_eqv_iso C C str str).to_fun ((_ ⬝e _).to_fun _),
  rwr equiv.to_fun_trans, 
  change _ = (@strict_cat_iso_eqv_iso C C str str).to_fun
        ((@Precat_id_equiv_iso C C str.to_is_precat str.to_is_precat)
        ((@strict_cat_eq_eqv_precat_eq (strict_Category.mk C str) (strict_Category.mk C str)).to_fun idp)),
  rwr strict_cat_idp_to_precat_idp, rwr precat_idp_equiv_id_iso, apply hom_eq_to_iso_eq, exact idp
end

end strict

open strict

@[hott, instance]
def strict_cat_is_cat : is_cat strict_Category :=
begin
  apply is_cat.mk, intros D₁ D₂, 
  change is_equiv (λ p, idtoiso p), 
  rwr eq_of_homotopy (@idtoiso_strictcattoiso D₁ D₂),
  apply_instance
end                 

@[hott]
def Strict_Categories : Category :=
  Category.mk strict_Category strict_cat_is_cat

@[hott, instance]
def Strict_Categories_are_strict_cat : Π (D : Strict_Categories), is_strict_cat D.obj :=
  λ D, strict_Category.strict_cat D 

@[hott, instance]
def Strict_Categories_is_cat : is_cat ↥Strict_Categories :=
  strict_cat_is_cat

/- Isomorphisms of strict catgeories can be cancelled in natural transformations. -/
@[hott]
def strict_cat_iso_lcancel {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C] (H : J₁ ≅ J₂) 
  {F G : J₂.obj ⥤ C} : ((H.hom ⋙ F) ⟹ (H.hom ⋙ G)) -> (F ⟹ G) :=
begin 
  intro H_nat_tr, fapply nat_trans.mk, 
  { intro j₂, exact F.map ((functor_eq_to_nat_trans (H.ih.r_inv⁻¹)).app j₂) ≫ 
                    H_nat_tr.app (H.ih.inv.obj j₂) ≫ 
                    G.map ((functor_eq_to_nat_trans H.ih.r_inv).app j₂) },
  { intros j₂ j₂' f, rwr <- is_precat.assoc (F.map f), rwr <- F.map_comp,
    change F.map ((𝟙 J₂ : J₂.obj ⥤ J₂.obj).map f ≫ _) ≫ _ ≫ _ = _,
    rwr (functor_eq_to_nat_trans (H.ih.r_inv)⁻¹).naturality f, rwr F.map_comp, rwr is_precat.assoc,
    rwr <- is_precat.assoc _ (H_nat_tr.app (H.ih.inv.obj j₂')), 
    change _ ≫ ((H.hom ⋙ F).map _ ≫ _) ≫ _ = _, rwr H_nat_tr.naturality, rwr is_precat.assoc,
    change _ ≫ _ ≫ G.map _ ≫ _ = _, rwr <- G.map_comp, 
    rwr is_precat.assoc _ _ (G.map f), rwr is_precat.assoc _ _ (G.map f), rwr <- G.map_comp, 
    change _ = _ ≫ _ ≫ G.map (_ ≫ ((𝟙 J₂ : J₂.obj ⥤ J₂.obj).map f)), 
    rwr <- (functor_eq_to_nat_trans H.ih.r_inv).naturality f }
end

end categories

end hott