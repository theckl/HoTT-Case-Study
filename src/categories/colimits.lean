import sets.finite categories.equalize 
       
universes v u v' u' w
hott_theory

namespace hott
open hott.is_trunc hott.trunc hott.set 
     hott.precategories hott.categories hott.categories.strict hott.categories.limits

/- We introduce colimits of diagrams mapped to categories, by using cocones to 
   pick the universal object and encode the universal property.

   As far as possible we copy the mathlib-code in [category_theory.limits]. -/

namespace categories.colimits

structure cocone {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat C] (F : J ⥤ C) :=
(X : C)
(π : F ⟹ (@constant_functor J _ C _ X))

@[hott]
structure is_colimit {J : Type _} [is_strict_cat J] {C : Type _} [is_precat C] 
  {F : J ⥤ C} (t : cocone F) :=
(desc : Π (s : cocone F), t.X ⟶ s.X)
(fac  : ∀ (s : cocone F) (j : J), t.π.app j ≫ desc s = s.π.app j)
(uniq : ∀ (s : cocone F) (m : t.X ⟶ s.X) 
          (w : ∀ j : J, t.π.app j ≫ m = s.π.app j), m = desc s)

@[hott] 
def desc_itself_id {J : Type _} [is_strict_cat J] {C : Type _} [is_precat C] 
  {F : J ⥤ C} {t : cocone F} (l : is_colimit t) : l.desc t = 𝟙 t.X :=
have t_fac : ∀ j : J, t.π.app j ≫ 𝟙 t.X = t.π.app j, by intro j; hsimp,  
(l.uniq _ _ t_fac)⁻¹             

@[hott]
def colimit_cocone_point_iso {J : Type _} [is_strict_cat J] {C : Type _} 
  [is_precat C] 
  {F : J ⥤ C} {s t : cocone F} (lₛ : is_colimit s) (lₜ : is_colimit t) : 
Σ i : t.X ≅ s.X, i.hom = lₜ.desc s :=
let st := lₜ.desc s, ts := lₛ.desc t in 
have s_fac : ∀ j : J, s.π.app j ≫ (ts ≫ st) = s.π.app j, from assume j,
  calc s.π.app j ≫ (ts ≫ st) = (s.π.app j ≫ ts) ≫ st : (is_precat.assoc _ _ _)⁻¹
       ... = t.π.app j ≫ st : by rwr lₛ.fac t j
       ... = s.π.app j : by rwr lₜ.fac s j,
have t_fac : ∀ j : J, t.π.app j ≫ (st ≫ ts) = t.π.app j, from assume j, 
  calc t.π.app j ≫ (st ≫ ts) = (t.π.app j ≫ st) ≫ ts : (is_precat.assoc _ _ _)⁻¹
       ... = s.π.app j ≫ ts : by rwr lₜ.fac s j 
       ... = t.π.app j : by rwr lₛ.fac t j,
have comp_s : ts ≫ st = 𝟙 s.X, from lₛ.uniq _ _ s_fac ⬝ desc_itself_id lₛ, 
have comp_t : st ≫ ts = 𝟙 t.X, from lₜ.uniq _ _ t_fac ⬝ desc_itself_id lₜ,
⟨iso.mk st (is_iso.mk ts comp_s comp_t), rfl⟩

/- `colimit_cocone F` contains a cocone over `F` together with the information that 
   it is a colimit. -/
@[hott]
structure colimit_cocone {J : Type _} [is_strict_cat J] {C : Type _} 
  [is_precat C] (F : J ⥤ C) :=
(cocone : cocone F)
(is_colimit : is_colimit cocone)

/- `has_colimit F` represents the mere existence of a colimit for `F`. This allows
   to define it as a class with instances. -/ 
@[hott]   
class has_colimit {J : Type _} [is_strict_cat J] {C : Type u} [is_precat.{v} C] 
  (F : J ⥤ C) :=
mk' :: (exists_colimit : ∥colimit_cocone F∥)

@[hott, instance]
def has_colimit_is_prop {J : Type _} [is_strict_cat J] {C : Type u} [is_precat.{v} C] 
  (F : J ⥤ C) : is_prop (has_colimit F) :=
begin 
  apply is_prop.mk, intros hcl₁ hcl₂, hinduction hcl₁, hinduction hcl₂,
  apply ap has_colimit.mk', exact is_prop.elim _ _ 
end

@[hott]
def has_colimit.mk {J : Type _} [is_strict_cat J] {C : Type u} [is_precat.{v} C] 
  {F : J ⥤ C} (d : colimit_cocone F) :=
has_colimit.mk' (tr d) 

/- If `C` is a category, the colimit cocone vertices of two instances of 
  `colimit_cocone F` are equal since they are determined up to isomorphism. Then 
   the "legs" of the cocones and the descendants of the universal property are 
   determined up to composition with the automorphism associated to this 
   equality of colimit cocone vertices, and colimit cocones are equal. 
   
   Thus, we can produce a `colimit_cocone F` from `has_colimit F`. -/
@[hott]
def colimit_cocone_is_unique {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_cat.{v} C] (F : J ⥤ C) : ∀ lc₁ lc₂ : colimit_cocone F, lc₁ = lc₂ :=
begin
  intros lc₁ lc₂, 
  hinduction lc₁ with cocone₁ is_colimit₁, hinduction lc₂ with cocone₂ is_colimit₂,
  have cocone_id : cocone₁ = cocone₂, from 
  begin
    hinduction cocone₁ with X₁ π₁, hinduction cocone₂ with X₂ π₂,  
    let lcp_iso := colimit_cocone_point_iso is_colimit₁ is_colimit₂,
    fapply apd011 cocone.mk,
    { exact idtoiso⁻¹ᶠ (inv_iso lcp_iso.1) },
    { hinduction π₁ with app₁ nat₁, hinduction π₂ with app₂ nat₂, 
      fapply apdo0111 (λ c : C, @nat_trans.mk _ _ _ _ F (@constant_functor J _ C _ c)),
      { apply pathover_of_tr_eq, apply eq_of_homotopy, 
        intro j, rwr tr_fn_tr_eval,
        change idtoiso⁻¹ᶠ (inv_iso lcp_iso.1) ▸[λ X : C, F.obj j ⟶ X] app₁ j = app₂ j,
        have r : idtoiso⁻¹ᶠ (inv_iso lcp_iso.1) ▸[λ X : C, F.obj j ⟶ X] app₁ j = 
                    app₁ j ≫ (inv_iso lcp_iso.1).hom, from
          @iso_hom_tr_comp' C _ _ X₁ X₂ (inv_iso lcp_iso.1) (app₁ j), 
        rwr r, apply inverse, apply iso_move_rl, exact (is_colimit₂.fac _ j) },
      { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros c c' f, 
        apply is_set.elim } }
  end,
  have is_colimit_id : is_colimit₁ =[cocone_id] is_colimit₂, from 
  begin 
    hinduction cocone_id,
    hinduction is_colimit₁ with desc₁ fac₁ uniq₁,
    hinduction is_colimit₂ with desc₂ fac₂ uniq₂, 
    fapply apdo01111 (@is_colimit.mk _ _ _ _ _),
    { apply pathover_of_tr_eq, hsimp, apply eq_of_homotopy, intro s,
      apply uniq₂, exact fac₁ s },
    { apply pathover_of_tr_eq, apply eq_of_homotopy2, intros s j, 
        apply is_set.elim },
    { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros s m id, 
        apply is_set.elim }
  end,
  fapply apd011 colimit_cocone.mk,
  { exact cocone_id },
  { exact is_colimit_id }
end  

@[hott, instance]
def colimit_cocone_is_prop {J : Type _} [is_strict_cat J] {C : Type u} [is_cat.{v} C] 
  (F : J ⥤ C) : is_trunc -1 (colimit_cocone F) :=
is_prop.mk (colimit_cocone_is_unique F)

@[hott]
def get_colimit_cocone {J : Type _} [is_strict_cat J] {C : Type u} [is_cat.{v} C] 
  (F : J ⥤ C) [has_colimit F] : colimit_cocone F :=
untrunc_of_is_trunc (has_colimit.exists_colimit F)  

@[hott]
def colimit.cocone {J : Type _} [is_strict_cat J] {C : Type u} [is_cat.{v} C]
  (F : J ⥤ C) [has_colimit F] : cocone F := (get_colimit_cocone F).cocone

@[hott]
def colimit {J : Type _} [is_strict_cat J] {C : Type u} [is_cat.{v} C]
  (F : J ⥤ C) [has_colimit F] := (colimit.cocone F).X

@[hott]
def diag_eq_colim_eq_colim {J : Strict_Categories} {C : Type _} [is_cat C]
  {F F' : J.obj ⥤ C} (p : F = F') [hlF : has_colimit F] : 
  colimit F = @colimit _ _ _ _ F' (p ▸ hlF) :=
fn2_ev_fn2_tr' p hlF (λ (F : J.obj ⥤ C) (hlF : has_colimit F), @colimit _ _ _ _ F hlF)


/- Colimits are natural under functors of shapes. In particular, colimits 
   of isomorphic shapes are naturally isomorphic. -/
@[hott]
def diag_eq_on_cocone {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (pJ : J₁ = J₂) (F : J₂.obj ⥤ C) : 
  (pJ⁻¹ ▸[λ J : Strict_Categories, J.obj ⥤ C] F) = ((idtoiso pJ).hom ⋙ F) :=
begin
  hinduction pJ, rwr idp_inv, rwr idp_tr, hsimp, 
  change F = ((id_functor J₁.obj) ⋙ F), rwr funct_id_comp
end

@[hott]
def diag_iso_on_cocone {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) (F : J₂.obj ⥤ C) : 
  ((category.isotoid H)⁻¹ ▸[λ J : Strict_Categories, J.obj ⥤ C] F) = (H.hom ⋙ F) :=
begin rwr diag_eq_on_cocone (category.isotoid H) F, rwr category.idtoiso_rinv' end

@[hott, instance, reducible]
def diag_iso_has_colim_to_has_colim {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} [hlF : has_colimit F] : 
  has_colimit ((category.isotoid H)⁻¹ ▸[λ J : Strict_Categories, J.obj ⥤ C] F) :=
begin
  let phl : @has_colimit _ J₂.strict_cat _ _ F = @has_colimit _ J₁.strict_cat _ _ 
                                      ((category.isotoid H)⁻¹ ▸[λ J : Strict_Categories, J.obj ⥤ C] F) := 
         fn2_ev_fn2_tr (category.isotoid H)⁻¹ F (λ (J : Strict_Categories) 
                                                   (F : J.obj ⥤ C), @has_colimit _ J.strict_cat _ _ F),
  exact phl ▸[id] hlF
end

@[hott, instance]
def diag_iso_has_colim_to_has_colim' {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} [hlF : has_colimit F] : has_colimit (H.hom ⋙ F) :=
begin rwr <- diag_iso_on_cocone H F, exact @diag_iso_has_colim_to_has_colim _ _ _ _ H F hlF end

@[hott]
def diag_iso_colim_eq_colim {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} [hlF : has_colimit F] : colimit F = colimit (H.hom ⋙ F) :=
begin
  change (λ (J : Strict_Categories) (F : J.obj ⥤ C) (hlF : @has_colimit _ J.strict_cat _ _ F), 
            @colimit _ J.strict_cat _ _ F hlF) J₂ F hlF = _,
  rwr fn3_ev_fn3_tr' (category.isotoid H)⁻¹ F hlF (λ (J : Strict_Categories) 
                (F : J.obj ⥤ C) (hlF : @has_colimit _ J.strict_cat _ _ F), @colimit _ J.strict_cat _ _ F hlF),
  exact diag_eq_colim_eq_colim (diag_iso_on_cocone H F)⁻¹⁻¹
end


/- More general classes of existence of colimits -/
@[hott]
class has_colimits_of_shape (J : Type _) [is_strict_cat J] (C : Type u) 
  [is_cat.{v} C] :=
(has_colimit : Π F : J ⥤ C, has_colimit F)

@[hott, priority 100, instance]
def has_colimit_of_has_colimits_of_shape {J : Type _} [is_strict_cat J]
  (C : Type u) [is_cat.{v} C] [H : has_colimits_of_shape J C] (F : J ⥤ C) : has_colimit F :=
has_colimits_of_shape.has_colimit F

@[hott]
class has_colimits (C : Type u) [is_cat.{v} C] :=
  (has_colimit_of_shape : Π (J : Type _) [is_strict_cat J], has_colimits_of_shape J C )

@[hott, instance]
def has_colimit_of_has_colimits (C : Type u) [is_cat.{v} C] [H : has_colimits C] 
  {J : Type _} [is_strict_cat J] (F : J ⥤ C) : has_colimit F :=
have H' : has_colimits_of_shape J C, from has_colimits.has_colimit_of_shape C J,  
@has_colimit_of_has_colimits_of_shape _ _ C _ H' F

@[hott]
class has_coproduct {C : Type u} [is_cat.{v} C] {J : Set.{u'}} (f : J -> C) := 
  (has_colimit : has_colimit (discrete.functor f)) 

@[hott, instance]
def has_coproduct_is_prop {C : Type u} [is_cat.{v} C] {J : Set.{u'}} (f : J -> C) :
  is_prop (has_coproduct f) :=
begin 
  apply is_prop.mk, intros hcp₁ hcp₂, hinduction hcp₁, hinduction hcp₂,
  apply ap has_coproduct.mk, exact is_prop.elim _ _ 
end  

@[hott, priority 100]
instance has_colimit_of_has_coproduct {C : Type u} [is_cat.{v} C] {J : Set.{u'}} 
  (f : J -> C) [has_coproduct f] : has_colimit (discrete.functor f) := 
has_coproduct.has_colimit f  

@[hott]
abbreviation copi_obj {C : Type u} [is_cat.{v} C] {J : Set.{u'}} (f : J → C) 
  [has_coproduct f] := 
colimit (discrete.functor f)

notation `⨿ ` f:20 := copi_obj f

@[hott]
class has_coproducts (C : Type u) [is_cat.{v} C] := 
  (has_colimit_of_shape : Π J : Set.{u'}, has_colimits_of_shape (discrete J) C)

@[hott, instance, priority 100]
def has_colimits_of_shape_of_has_coproducts (J : Set.{u'}) (C : Type u) [is_cat.{v} C] 
  [has_coproducts.{v u u'} C] : has_colimits_of_shape (discrete J) C :=
has_coproducts.has_colimit_of_shape C J

@[hott]
instance has_coproduct_of_has_coproducts {C : Type u} [is_cat.{v} C] 
  [has_coproducts C] {J : Set.{u'}} (f : J -> C) : has_coproduct f :=
⟨@has_colimits_of_shape.has_colimit _ _ _ _ 
       (has_coproducts.has_colimit_of_shape C J) (discrete.functor f)⟩

@[hott, instance]
def has_coproduct_of_has_colimits_of_shape {C : Type u} [is_cat.{v} C] 
  {J : Set.{u'}} [has_colimits_of_shape (discrete J) C] (f : J -> C) : 
  has_coproduct f :=
⟨has_colimits_of_shape.has_colimit (discrete.functor f)⟩ 

@[hott, instance]
def has_coproducts_of_has_colimits (C : Type u) [is_cat.{v} C] [c : has_colimits C] : 
  has_coproducts C :=
has_coproducts.mk (λ J, @has_colimits.has_colimit_of_shape C _ c (discrete J) _)

/-- A cofan over `f : J → C` consists of a collection of maps from every `f j` to an object
    `CP`. This is enough to determine a cocone which factorizes through the coproduct. -/
@[hott]    
abbreviation cofan {J : Set.{u'}} {C : Type u} [is_cat.{v} C] (f : J → C) := 
  cocone (discrete.functor f)

@[hott, hsimp]
def cofan.mk {J : Set.{u'}} (C : Type u) [is_cat.{v} C] {f : J → C} {CP : C} 
  (p : Π j, f j ⟶ CP) : cofan f :=
cocone.mk CP (discrete.nat_trans p)

@[hott, hsimp] 
def copi.desc {J : Set.{u'}} {C : Type u} [is_cat.{v} C] {f : J → C} [has_coproduct f]
  {CP : C} (p : Π j, f j ⟶ CP) : ⨿ f ⟶ CP :=
(get_colimit_cocone (discrete.functor f)).is_colimit.desc (cofan.mk _ p)  

@[hott, hsimp] 
def copi.π {J : Set.{u'}} {C : Type u} [is_cat.{v} C] (f : J → C) [has_coproduct f] 
  (j : J) : f j ⟶ ⨿ f :=
(colimit.cocone (discrete.functor f)).π.app j 

@[hott]
def copi.hom_is_desc {J : Set.{u'}} {C : Type u} [is_cat.{v} C] {f : J → C} 
  [has_coproduct f] {CP : C} (h : ⨿ f ⟶ CP) : h = copi.desc (λ j : J, (copi.π _ j) ≫ h) :=
let p := λ j : J, (copi.π f j) ≫ h, c := cofan.mk _ p,
    clc := get_colimit_cocone (discrete.functor f) in     
begin 
  change h = clc.is_colimit.desc c, 
  apply is_colimit.uniq clc.is_colimit c h, 
  intro j, exact rfl, 
end  

@[hott]
def copi.desc_π_eq {J : Set.{u'}} (C : Type u) [is_cat.{v} C] {f : J → C} 
  [has_coproduct f] {CP : C} (p : Π j : J, f j ⟶ CP) : 
  ∀ j : J, (copi.π _ j) ≫ (copi.desc p) = p j :=
assume j, by apply is_colimit.fac  

@[hott]
def copi.desc_fac {J : Set.{u'}} {C : Type u} [is_cat.{v} C] {f : J → C} 
  [has_coproduct f] {CP CQ : C} (g : CP ⟶ CQ) (h : Π j : J, f j ⟶ CP) :
  copi.desc (λ j, h j ≫ g) = copi.desc h ≫ g :=
let p := λ j : J, h j ≫ g, c := cofan.mk _ p, 
    clc := get_colimit_cocone (discrete.functor f) in  
begin 
  apply eq.inverse, apply is_colimit.uniq clc.is_colimit c, intro j, 
  change copi.π _ j ≫ copi.desc h ≫ g = c.π.app j, rwr <- is_precat.assoc, 
  rwr copi.desc_π_eq _ h
end  

@[hott]
def copi.uniq {J : Set.{u'}} {C : Type u} [is_cat.{v} C] {f : J → C} 
  [has_coproduct f] {c : C} (h : Π j : J, f j ⟶ c) (g : ⨿ f ⟶ c) : 
  (Π j : J, copi.π f j ≫ copi.desc h = copi.π f j ≫ g) -> g = copi.desc h :=
let p := λ j : J, h j, c := cofan.mk _ p, 
    clc := get_colimit_cocone (discrete.functor f) in   
begin
  intro desc_eq, apply is_colimit.uniq clc.is_colimit c, intro j,
  change copi.π f j ≫ g = h j, rwr <- desc_eq j, exact copi.desc_π_eq _ h j
end

@[hott]
def copi_hom {J : Set.{u'}} {C : Type u} [is_cat.{v} C] [has_coproducts.{v u u'} C] 
  {f g : J -> C} (h : Π j : J, f j ⟶ g j) : ⨿ f ⟶ ⨿ g :=
copi.desc (λ j : J, h j ≫ copi.π g j )

notation `⨿h ` h:20 := copi_hom h

@[hott]
def copi_hom_id {J : Set.{u'}} {C : Type u} [is_cat.{v} C] [has_coproducts.{v u u'} C] 
  (f : J -> C) : copi_hom (λ j, 𝟙 (f j)) = 𝟙 (⨿ f) :=
have H : (λ j, 𝟙 (f j) ≫ copi.π f j ) = λ j, copi.π f j ≫ 𝟙 (⨿ f), from 
  begin apply eq_of_homotopy, intro j, hsimp end,  
begin change copi.desc (λ j, 𝟙 (f j) ≫ copi.π f j) = _, rwr H, rwr <- copi.hom_is_desc end  

@[hott]
def copi_hom_comp {J : Set.{u'}} {C : Type u} [is_cat.{v} C] [has_coproducts.{v u u'} C] 
  {f g h : J -> C}  (i₁ : Π j : J, f j ⟶ g j)  (i₂ : Π j : J, g j ⟶ h j) :
  (⨿h i₁) ≫ (⨿h i₂) = ⨿h (λ j, i₁ j ≫ i₂ j) :=
have H : (λ j, (i₁ j ≫ copi.π g j) ≫ copi.desc (λ k, i₂ k ≫ copi.π h k)) = 
                                                  λ j, (i₁ j ≫ i₂ j) ≫ copi.π h j, from   
  begin 
    apply eq_of_homotopy, intro j, 
    change (i₁ j ≫ copi.π g j) ≫ copi.desc (λ k, i₂ k ≫ copi.π h k) = 
                                                           (i₁ j ≫ i₂ j) ≫ copi.π h j, 
    rwr is_precat.assoc, rwr copi.desc_π_eq, rwr is_precat.assoc
  end,
calc (⨿h i₁) ≫ (⨿h i₂) =
     copi.desc (λ j, i₁ j ≫ copi.π g j) ≫ copi.desc (λ j, i₂ j ≫ copi.π h j) : rfl 
     ... = copi.desc (λ j, (i₁ j ≫ copi.π g j) ≫ copi.desc (λ j, i₂ j ≫ copi.π h j)) : 
                                                                  by rwr <- copi.desc_fac                                                             
     ... = copi.desc (λ j, (i₁ j ≫ i₂ j) ≫ copi.π h j) : by rwr H
     ... = ⨿h (λ j, i₁ j ≫ i₂ j) : by refl


/- Unions of subobjects of a given object in a category can be defined as colimits in the 
   category of such subobjects. Note that this is not the colimit in the surrounding 
   category but the image of the natural homomorphism to the containing object. Therefore,
   having colimits in the surrounding category is not enough for the existence of unions; we 
   also need the existence of images. 
   
   We also separately exhibit finite unions, for use in categorical models, and we 
   introduce the union of two subobjects, to make use of the notation `∪`. -/
@[hott]
class has_subobj_union {C : Type u} [is_cat.{v} C] {c : C} {J : Set.{u'}} (f : J -> subobject c) :=
  (exists_union : @has_coproduct _ subobject_is_cat _ f) 

@[hott, instance]
def has_so_union_is_prop {C : Type u} [is_cat.{v} C] {c : C} {J : Set.{u'}} 
  (f : J -> subobject c) : is_prop (has_subobj_union f) :=
begin 
  apply is_prop.mk, intros hsu₁ hsu₂, hinduction hsu₁, hinduction hsu₂,
  apply ap has_subobj_union.mk, exact is_prop.elim _ _ 
end

@[hott, instance]
def has_subobj_union_of_has_coproducts_and_images {C : Type u} [is_cat.{v} C] 
  [has_coproducts.{v u u'} C] [has_images C] {c : C} {J : Set.{u'}} 
  (f : J -> subobject.{u v} c) : has_subobj_union f :=
begin 
  apply has_subobj_union.mk, apply has_coproduct.mk, apply has_colimit.mk,
  fapply colimit_cocone.mk, 
  { fapply cofan.mk, 
    { exact hom.image (copi.desc (λ j : J, (f j).hom)) }, 
    { intro j, fapply hom_of_monos.mk,
      { exact copi.π _ j ≫ hom_to_image _ },
      { rwr is_precat.assoc, rwr hom_to_image_eq, rwr copi.desc_π_eq } } },
  { fapply is_colimit.mk, 
    { intro cocone_f, change ↥(hom.image (copi.desc (λ j : J, (f j).hom)) ⟶ _),
      let cf : Π j : J, (f j).obj ⟶ cocone_f.X.obj := 
                                             λ j : J, (cocone_f.π.app j).hom_obj,
      fapply hom_image_univ, 
      { exact copi.desc cf },
      { apply copi.uniq, intro j, rwr <- is_precat.assoc, rwr copi.desc_π_eq, 
        rwr copi.desc_π_eq, rwr (cocone_f.π.app j).fac } }, 
    { intros cf j, exact is_prop.elim _ _ }, 
    { intros cf m w, exact is_prop.elim _ _ } }
end

@[hott, instance]
def has_union_to_has_coproduct {C : Type u} [is_cat.{v} C] {c : C} {J : Set} 
  (f : J -> subobject c) [H : has_subobj_union f] : has_coproduct f := H.exists_union

@[hott]
def subobject.union {C : Type u} [is_cat.{v} C] {c : C} {J : Set} (f : J -> subobject c)
  [has_subobj_union f] := ⨿ f

@[hott]
class has_unions (C : Type u) [is_cat.{v} C] :=
  (has_union : Π {c : C} {J : Set} (f : J -> subobject c), has_subobj_union f)

@[hott, instance]
def has_union_of_has_unions {C : Type u} [is_cat.{v} C] {c : C} [has_unions C] 
  {J : Set} (f : J -> subobject c) : has_subobj_union f :=
has_unions.has_union f 

@[hott]
def union_inc {C : Type u} [is_cat.{v} C] {c : C} {J : Set} (f : J -> subobject c)
  [has_subobj_union f] : Π j : J, f j ≼ subobject.union f :=
assume j, copi.π f j

@[hott]
def union_fac {C : Type u} [is_cat.{v} C] {c : C} {J : Set} (f : J -> subobject c)
  [has_subobj_union f] {u : subobject c} (h : Π j, f j ≼ u) : subobject.union f ≼ u :=
copi.desc h    

@[hott]
class has_fin_union {C : Type u} [is_cat.{v} C] {c : C} {n : ℕ} (f : fin_Set n -> subobject c) :=
(exists_union : has_subobj_union f)

@[hott, instance]
def has_fin_union_is_prop {C : Type u} [is_cat.{v} C] {c : C} {n : ℕ} (f : fin_Set n -> subobject c) : 
  is_prop (has_fin_union f) :=
begin 
  apply is_prop.mk, intros hfu₁ hfu₂, hinduction hfu₁, hinduction hfu₂,
  apply ap has_fin_union.mk, exact is_prop.elim _ _ 
end

@[hott, instance]
def has_union_of_has_fin_union {C : Type u} [is_cat.{v} C] {c : C} {n : ℕ} 
  (f : fin_Set n -> subobject c) [H : has_fin_union f] : has_subobj_union f :=
H.exists_union

@[hott]
class has_fin_unions (C : Type u) [is_cat.{v} C] :=
  (has_fin_union : Π (c : C) {n : ℕ} (f : fin_Set n -> subobject c), has_fin_union f)

@[hott, instance]
def has_fin_unions_is_prop {C : Type u} [is_cat.{v} C] : 
  is_prop (has_fin_unions C) :=
begin 
  apply is_prop.mk, intros hfu₁ hfu₂, hinduction hfu₁, hinduction hfu₂,
  apply ap has_fin_unions.mk, exact is_prop.elim _ _ 
end

@[hott, instance]
def has_fin_union_of_has_fin_unions {C : Type u} [is_cat.{v} C] [has_fin_unions C] {c : C} 
  {n : ℕ} (f : fin_Set n -> subobject c) : has_fin_union f :=
has_fin_unions.has_fin_union c f   

@[hott, instance]
def has_fin_unions_of_has_unions (C : Type u) [is_cat.{v} C] [H : has_unions C] : has_fin_unions C :=
  has_fin_unions.mk (λ c n f, (has_fin_union.mk (@has_unions.has_union C _ H _ _ f)))

@[hott, instance]
def subobj_has_union {C : Type u} [is_cat.{v} C] {c : C} [has_fin_unions C] :
  has_union (subobject c) :=
has_union.mk (λ a b, subobject.union (fin_map_of_list [a, b]))

/- If finite unions exist every category of subobjects also has a bottom element, produced 
   as the empty union. -/
@[hott]
def bottom_subobject {C : Type u} [is_cat.{v} C] (c : C) [has_fin_unions C] : 
  subobject c :=
subobject.union (empty_fin_Set_map (subobject c))

@[hott] 
def bottom_subobj_prop {C : Type u} [is_cat.{v} C] {c : C} [has_fin_unions C] : 
  Π (a : subobject c), bottom_subobject c ≼ a :=
begin intro a, fapply union_fac, intro j, hinduction hott.nat.not_lt_zero j.1 j.2 end   

/- Universal property of unions of subobjects -/
@[hott]
def lift_to_union {C : Type u} [is_cat.{v} C] {d : C} [has_fin_unions C] : Π {a b c : subobject d},
  a ≼ c -> b ≼ c -> a ∪ b ≼ c :=
begin 
  intros a b c i₁ i₂, fapply union_fac (fin_map_of_list [a, b]), 
  intro j, hinduction j with n ineq, hinduction n, 
  { have p : fin_map_of_list [a, b] ⟨0, ineq⟩ = a, by rwr <- fin_map_of_list_el,
    rwr p, exact i₁ }, 
  { hinduction n, 
    {  have q : fin_map_of_list [a, b] ⟨1, ineq⟩ = b, by rwr <- fin_map_of_list_el,
       rwr q, exact i₂ },
    { change _ < nat.succ 1 at ineq, 
      hinduction nat.not_lt_zero n (nat.le_of_succ_le_succ (nat.le_of_succ_le_succ ineq)) } }
end 

/- The natural inclusions into the union -/
@[hott]
def subobj_union_rinc {C : Type u} [is_cat.{v} C] {c : C} [has_fin_unions C]
  (a b : subobject c) : b ≼ a ∪ b :=
begin
  have ineq1 : 1 < 2, from nat.lt.base 1,
  have q : fin_map_of_list [a, b] ⟨1, ineq1⟩ = b, by rwr <- fin_map_of_list_el, 
  rwr <- q, fapply union_inc (fin_map_of_list [a, b]) ⟨1, ineq1⟩
end

@[hott]
def subobj_union_linc {C : Type u} [is_cat.{v} C] {c : C} [has_fin_unions C]
  (a b : subobject c) : a ≼ a ∪ b :=
begin
  have ineq0 : 0 < 2, from nat.lt_trans (nat.lt.base 0) (nat.lt.base 1),
  have p : fin_map_of_list [a, b] ⟨0, ineq0⟩ = a, by rwr <- fin_map_of_list_el, 
  rwr <- p, fapply union_inc (fin_map_of_list [a, b]) ⟨0, ineq0⟩
end

@[hott]
def univ_char_of_union {C : Type u} [is_cat.{v} C] {d : C} [has_fin_unions C] : 
  Π {a b c : subobject d}, (a ≼ c) -> (b ≼ c) -> 
       (Π c' : subobject d, (a ≼ c') -> (b ≼ c') -> c ≼ c') -> (c = a ∪ b) :=
begin
  intros a b c ac bc minc, 
  fapply subobj_antisymm,
  { exact minc (a ∪ b) (subobj_union_linc _ _) (subobj_union_rinc _ _) },
  { exact lift_to_union ac bc }
end

@[hott]
def subobj_hom_union_absorb {C : Type u} [is_cat.{v} C] {c : C} [has_fin_unions C] {a b : subobject c} : 
  a ≼ b -> a ∪ b = b :=
begin
  intro ineq, fapply subobj_antisymm,
  { fapply lift_to_union, exact ineq, exact 𝟙 b },
  { exact subobj_union_rinc _ _ }
end 

@[hott]
def bottom_union_absorb {C : Type u} [is_cat.{v} C] {c : C} [has_fin_unions C] (a : subobject c) : 
  (bottom_subobject c) ∪ a = a :=
subobj_hom_union_absorb (bottom_subobj_prop a)

/- Associativity of unions of subobjects -/
@[hott]
def union_assoc {C : Type u} [is_cat.{v} C] {d : C} [has_fin_unions C] : Π {a b c : subobject d},
  (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
begin
  intros a b c, fapply subobj_antisymm, 
  { fapply lift_to_union, 
    { fapply lift_to_union, 
      { exact subobj_union_linc _ _ },
      { exact subobj_trans (subobj_union_linc b c) (subobj_union_rinc a (b ∪ c)) } },
    { exact subobj_trans (subobj_union_rinc b c) (subobj_union_rinc a (b ∪ c)) } },
  { fapply lift_to_union, 
    { exact subobj_trans (subobj_union_linc a b) (subobj_union_linc (a ∪ b) c) },
    { fapply lift_to_union, 
      { exact subobj_trans (subobj_union_rinc a b) (subobj_union_linc (a ∪ b) c) },
      { exact subobj_union_rinc _ _ } } }
end 

/- Commutativity of unions of subobjects -/
@[hott]
def union_comm {C : Type u} [is_cat.{v} C] {c : C} [has_fin_unions C] : Π (a b : subobject c),
  a ∪ b = b ∪ a :=
begin
  intros a b, fapply subobj_antisymm,
  { fapply lift_to_union,
    { exact subobj_union_rinc _ _ },
    { exact subobj_union_linc _ _ } },
  { fapply lift_to_union,
    { exact subobj_union_rinc _ _ },
    { exact subobj_union_linc _ _ } }
end

/- We introduce the initial object in a category together with some of its properties; 
  it exists if the category has colimits. -/
@[hott]
class initial (C : Type u) [is_cat.{v} C] := 
  (init_obj : C)
  (init_map : Π (c : C), init_obj ⟶ c)
  (uniq : Π {c : C} (f g : init_obj ⟶ c), f = g)

@[hott, instance]
def has_initial_of_has_coproduct (C : Type u) [is_cat.{v} C] 
  [H : has_coproduct (empty_map.{u u} C)] : initial C :=
begin
  fapply initial.mk,
  { exact @copi_obj _ _ _ (empty_map C) H },
  { intro c, apply copi.desc, intro j, hinduction j },
  { intros c f g, 
    let cc := @cofan.mk _ C _ (empty_map.{u u} C) c (λ j : false, false.rec _ j),
    let lcc := (get_colimit_cocone (discrete.functor (empty_map.{u u} C))).cocone,
    have mcf : Π j, lcc.π.app j ≫ f = cc.π.app j, from begin intro j, hinduction j end,
    have mcg : Π j, lcc.π.app j ≫ g = cc.π.app j, from begin intro j, hinduction j end,
    let p := (get_colimit_cocone (discrete.functor (empty_map.{u u} C))).is_colimit.uniq, 
    rwr p cc f mcf, rwr p cc g mcg }
end

@[hott]
def initial_map_is_epi (C : Type u) [is_cat.{v} C] [H : initial C] {c : C} :
  Π (f : c ⟶ H.init_obj), is_epi f :=
begin intros f d g₁ g₂ p, apply H.uniq end

/- A zero object in a category is both initial and terminal, but it can happen that in a category 
   (for example, the category of sets) there exist both initial and terminal object but they are not equal.
   Therefore, existence of limits and colimits does not imply the existence of a zero object. -/
@[hott]
class zero (C : Type u) [is_cat.{v} C] := 
  (obj : C)
  (init_map : Π (c : C), obj ⟶ c)
  (init_uniq : Π {c : C} (f g : obj ⟶ c), f = g)
  (term_map : Π (c : C), c ⟶ obj)
  (term_uniq : Π {c : C} (f g : c ⟶ obj), f = g)

@[hott, instance]
def zero_is_initial (C : Type u) [is_cat.{v} C] [H : zero C] : initial C :=
  initial.mk H.obj zero.init_map (@zero.init_uniq _ _ H) 

@[hott, instance]
def zero_is_terminal (C : Type u) [is_cat.{v} C] [H : zero C] : terminal C :=
  terminal.mk H.obj zero.term_map H.term_uniq 

@[hott]
def zero_init_map_is_epi (C : Type u) [is_cat.{v} C] [H : zero C] {c : C} :
  Π (f : c ⟶ H.obj), is_epi f :=
begin intros f d g₁ g₂ p, apply H.init_uniq end

@[hott]
def zero_term_map_is_mono (C : Type u) [is_cat.{v} C] [H : zero C] {c : C} :
  Π (f : H.obj ⟶ c), is_mono f :=
begin intros f d g₁ g₂ p, apply H.term_uniq end

@[hott]
def zero_subobj (C : Type u) [is_cat.{v} C] [H : zero C] {c : C} : subobject c := 
  subobject.mk H.obj (zero.init_map c) (zero_term_map_is_mono C (zero.init_map c))

@[hott]
def zero_map {C : Type u} [is_cat.{v} C] [H : zero C] (c d : C) : c ⟶ d :=
  zero.term_map c ≫ zero.init_map d 

end categories.colimits

open categories.colimits

@[hott]
class is_ker_subobject {C : Type u} [is_cat.{v} C] [zero C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) (ker : subobject c₁) :=
  (equal : is_equalizer f (zero_map c₁ c₂) ker.hom) 

@[hott]
class is_kernel {C : Type u} [is_cat.{v} C] [zero C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) (ker : C) :=
  (hom : ker ⟶ c₁)
  (mon : is_mono hom)
  (is_ker : is_ker_subobject f (subobject.mk ker hom mon))

end hott