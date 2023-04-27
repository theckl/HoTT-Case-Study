import sets.algebra init2 types2 sets.axioms categories.basic

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.eq hott.sigma hott.set hott.subset hott.is_trunc 
     hott.is_equiv hott.precategories hott.categories


/- The fully embedded category of a type injectively mapped to a category. 
   We start with a synonym for an (embedded) type `D`, on which the category structure
   will be defined, as in [category_theory.full_subcategory] of the mathlib. -/
@[hott]
def ind_cat_type {C : Category} {D : Type u'} (f : D -> C) := D

@[hott, instance]
def mapped_type_has_hom {C : Category} {D : Type u'} (f : D -> C) : 
  has_hom (ind_cat_type f) :=
begin fapply has_hom.mk, intros d₁ d₂, exact f d₁ ⟶ f d₂ end  

@[hott]
def ind_type_hom_hom {C : Category} {D : Type u'} (f : D -> C)
  {d₁ d₂ : ind_cat_type f} : (d₁ ⟶ d₂) -> (f d₁ ⟶ f d₂) := 
assume h, h  

@[hott, instance]
def ind_type_cat_struct {C : Category} {D : Type u'} (f : D -> C) : 
  category_struct (ind_cat_type f) :=
begin
  fapply category_struct.mk,
  { intro a, exact 𝟙 (f a) },
  { intros a b c f g, exact f ≫ g }
end  

@[hott, instance]
def fully_ind_precategory {C : Category} {D : Type u'} (f : D -> C) : 
  is_precat (ind_cat_type f) :=
begin
  fapply is_precat.mk,
  { intros d₁ d₂ f, hsimp },
  { intros d₁ d₂ f, hsimp },
  { intros d₁ d₂ d₃ d₄ f g h, hsimp, refl }
end  

@[hott]
def ind_type_iso_iso {C : Category} {D : Type u'} (f : D -> C)
  {d₁ d₂ : ind_cat_type f} : (d₁ ≅ d₂) -> (f d₁ ≅ f d₂) := 
begin
  intro i, fapply iso.mk,  
  { exact i.hom }, fapply is_iso.mk,
  { exact i.ih.inv },
  { exact i.ih.r_inv },
  { exact i.ih.l_inv }
end  

@[hott]
def ind_idtoiso_hom {C : Category} {D : Type u'} (f : D -> C)
  (inj : is_injective (λ d : ind_cat_type f, f d)) {d₁ d₂ : ind_cat_type f} : 
  Π p : f d₁ = f d₂, (idtoiso (inj_imp inj d₁ d₂ p)).hom = (idtoiso p).hom :=
begin 
  fapply equiv_arg_exchange,
  { exact d₁ = d₂ },
  { intro p, exact ap f p },
  { exact inj d₁ d₂ },
  { intro q, fapply @eq.rec _ d₁ (λ d₂, λ q : d₁ = d₂, 
               (idtoiso (inj_imp inj d₁ d₂ (ap f q))).hom = (idtoiso (ap f q)).hom), 
    change (idtoiso (inj_imp inj d₁ d₁ (ap f (refl d₁)))).hom = 𝟙 d₁, 
    have H : inj_imp inj d₁ d₁ (ap f (refl d₁)) = refl d₁, from
      @is_equiv.left_inv _ _ _ (inj d₁ d₁) (refl d₁), 
    rwr H }
end

@[hott, instance]
def fully_embedded_category {C : Category} {D : Type u'} (f : D -> C)
  [inj : is_injective f] : is_cat (ind_cat_type f) :=
begin
  fapply is_cat.mk,
  intros d₁ d₂, fapply adjointify, 
  { intro i, exact inj_imp inj d₁ d₂ (category.isotoid (ind_type_iso_iso f i)) },
  { intro i, apply hom_eq_to_iso_eq, 
    rwr ind_idtoiso_hom f inj (category.isotoid (ind_type_iso_iso f i)),
    change (idtoiso (idtoiso⁻¹ᶠ (ind_type_iso_iso f i))).hom = i.hom,
    rwr category.idtoiso_rinv (ind_type_iso_iso f i) },
  { intro p, hinduction p, rwr idtoiso_refl_eq d₁, 
    have H : ind_type_iso_iso f (id_iso d₁) = id_iso (f d₁), from 
      begin apply hom_eq_to_iso_eq, refl end,
    rwr H, rwr isotoid_id_refl, exact @inj_idp _ _ _ inj d₁ }
end    

@[hott]
def emb_functor {C : Category} {D : Type u'} (f : D -> C) : 
  (ind_cat_type f) ⥤ C :=
begin
  fapply precategories.functor.mk,
  { exact f },
  { intros x y h, exact h },
  { intro x, refl },
  { intros x y z g h, refl }
end  

/- The full subcategory on a subtype of the type of a category can be defined using
   the injective embedding of the subtype into the type. -/
@[hott]
def subtype_emb {C : Type _} [is_cat C] (P : C -> trunctype.{0} -1) :
  subtype (λ c : C, ↥(P c)) -> C := assume sc, sc.1

@[hott, instance]
def subtype_emb_is_inj {C : Type _} [is_cat C] (P : C -> trunctype.{0} -1) :
  is_injective (subtype_emb P) :=
begin intros sc₁ sc₂, exact (subtype_eq_equiv sc₁ sc₂).to_is_equiv end    

@[hott, instance]
def full_subcat_on_subtype {C : Type _} [H : is_cat C] (P : C -> trunctype.{0} -1) :
  is_cat (subtype (λ c : C, ↥(P c))) :=
@fully_embedded_category (Category.mk C H) _ (subtype_emb P) (subtype_emb_is_inj P)  

@[hott]
def embed {C : Type _} [HC : is_cat C] {P : C -> trunctype.{0} -1} 
  {D : Type _} [H : is_precat D] (F : D ⥤ subtype (λ c : C, ↥(P c))) : D ⥤ C :=
have G : subtype (λ c : C, ↥(P c)) ⥤ C, from 
  @emb_functor (Category.mk C HC) _ (subtype_emb P), 
F ⋙ G 

end hott