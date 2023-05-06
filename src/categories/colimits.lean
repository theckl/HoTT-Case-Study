import sets.algebra categories.examples categories.strict_cat categories.limits 
       sets.quotients sets.finite

universes v u v' u' w
hott_theory

namespace hott
open hott.eq hott.is_trunc hott.trunc hott.set hott.subset 
     hott.precategories hott.categories hott.categories.strict 

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
class has_colimit {J : Type _} [is_strict_cat J] {C : Type _} [is_precat C] 
  (F : J ⥤ C) :=
mk' :: (exists_colimit : ∥colimit_cocone F∥)

@[hott]
def has_colimit.mk {J : Type _} [is_strict_cat J] {C : Type _} [is_precat C] 
  {F : J ⥤ C} (d : colimit_cocone F) :=
has_colimit.mk' (tr d) 

/- If `C` is a category, the colimit cocone vertices of two instances of 
  `colimit_cocone F` are equal since they are determined up to isomorphism. Then 
   the "legs" of the cocones and the descendants of the universal property are 
   determined up to composition with the automorphism associated to this 
   equality of colimit cocone vertices, and colimit cocones are equal. 
   
   Thus, we can produce a `colimit_cocone F` from `has_colimit F`. -/
@[hott]
def colimit_cocone_is_unique {J : Type _} [is_strict_cat J] {C : Type _} 
  [is_cat C] (F : J ⥤ C) : ∀ lc₁ lc₂ : colimit_cocone F, lc₁ = lc₂ :=
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
          @iso_hom_tr_comp' (Category.mk C _) X₁ X₂ _ (inv_iso lcp_iso.1) (app₁ j), 
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
def colimit_cocone_is_prop {J : Type _} [is_strict_cat J] {C : Type _} [is_cat C] 
  (F : J ⥤ C) : is_trunc -1 (colimit_cocone F) :=
is_prop.mk (colimit_cocone_is_unique F)

@[hott]
def get_colimit_cocone {J : Type _} [is_strict_cat J] {C : Type _} [is_cat C] 
  (F : J ⥤ C) [has_colimit F] : colimit_cocone F :=
untrunc_of_is_trunc (has_colimit.exists_colimit F)  

@[hott]
def colimit.cocone {J : Type _} [is_strict_cat J] {C : Type _} [is_cat C]
  (F : J ⥤ C) [has_colimit F] : cocone F := (get_colimit_cocone F).cocone

@[hott]
def colimit {J : Type _} [is_strict_cat J] {C : Type _} [is_cat C]
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
  let phl : has_colimit F = has_colimit ((category.isotoid H)⁻¹ ▸[λ J : Strict_Categories, 
                                        J.obj ⥤ C] F) := 
         fn2_ev_fn2_tr (category.isotoid H)⁻¹ F (λ (J : Strict_Categories) 
                                                   (F : J.obj ⥤ C), has_colimit F),
  exact phl ▸[id] hlF
end

@[hott, instance]
def diag_iso_has_colim_to_has_colim' {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} [hlF : has_colimit F] : has_colimit (H.hom ⋙ F) :=
begin rwr <- diag_iso_on_cocone H F, exact @diag_iso_has_colim_to_has_colim _ _ _ _ H F hlF end

@[hott]
def diag_iso_colim_eq_colim {J₁ J₂ : Strict_Categories} {C : Type _} [is_cat C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} [hlF : has_colimit F] : colimit F = colimit (H.hom ⋙ F) :=
begin
  change (λ (J : Strict_Categories) (F : J.obj ⥤ C) (hlF : has_colimit F), 
            @colimit _ _ _ _ F hlF) J₂ F hlF = _,
  rwr fn3_ev_fn3_tr' (category.isotoid H)⁻¹ F hlF (λ (J : Strict_Categories) 
                          (F : J.obj ⥤ C) (hlF : has_colimit F), @colimit _ _ _ _ F hlF),
  exact diag_eq_colim_eq_colim (diag_iso_on_cocone H F)⁻¹⁻¹
end


/- More general classes of existence of colimits -/
@[hott]
class has_colimits_of_shape (J : Type _) [is_strict_cat J] (C : Type _) 
  [is_cat C] :=
(has_colimit : Π F : J ⥤ C, has_colimit F)

@[hott, priority 100, instance]
def has_colimit_of_has_colimits_of_shape {J : Type _} [is_strict_cat J]
  (C : Type _) [is_cat C] [H : has_colimits_of_shape J C] (F : J ⥤ C) : has_colimit F :=
has_colimits_of_shape.has_colimit F

@[hott]
class has_colimits (C : Type _) [is_cat C] :=
  (has_colimit_of_shape : Π (J : Type _) [is_strict_cat J], has_colimits_of_shape J C )

@[hott, instance]
def has_colimit_of_has_colimits (C : Type _) [is_cat C] [H : has_colimits C] 
  {J : Type _} [is_strict_cat J] (F : J ⥤ C) : has_colimit F :=
have H' : has_colimits_of_shape J C, from has_colimits.has_colimit_of_shape C J,  
@has_colimit_of_has_colimits_of_shape _ _ C _ H' F

@[hott]
class has_coproduct {C : Type _} [is_cat C] {J : Set} (f : J -> C) := 
  (has_colimit : has_colimit (discrete.functor f)) 

@[hott, priority 100]
instance has_colimit_of_has_coproduct {C : Type _} [is_cat C] {J : Set} 
  (f : J -> C) [has_coproduct f] : has_colimit (discrete.functor f) := 
has_coproduct.has_colimit f  

@[hott]
abbreviation copi_obj {C : Type _} [is_cat C] {J : Set} (f : J → C) 
  [has_coproduct f] := 
colimit (discrete.functor f)

notation `⨿ ` f:20 := copi_obj f

@[hott]
class has_coproducts (C : Type u) [is_cat.{v} C] := 
  (has_colimit_of_shape : Π J : Set, has_colimits_of_shape (discrete J) C)

@[hott, instance, priority 100]
def has_colimits_of_shape_of_has_coproducts (J : Set) (C : Type _) [is_cat C] 
  [has_coproducts C] : has_colimits_of_shape (discrete J) C :=
has_coproducts.has_colimit_of_shape C J

@[hott]
instance has_coproduct_of_has_coproducts {C : Type _} [is_cat C] 
  [has_coproducts C] {J : Set} (f : J -> C) : has_coproduct f :=
⟨@has_colimits_of_shape.has_colimit _ _ _ _ 
       (has_coproducts.has_colimit_of_shape C J) (discrete.functor f)⟩

@[hott, instance]
def has_coproduct_of_has_climits_of_shape {C : Type _} [is_cat C] 
  {J : Set} [has_colimits_of_shape (discrete J) C] (f : J -> C) : 
  has_coproduct f :=
⟨has_colimits_of_shape.has_colimit (discrete.functor f)⟩ 

@[hott, instance]
def has_coproducts_of_has_colimits (C : Type _) [is_cat C] [c : has_colimits C] : 
  has_coproducts C :=
has_coproducts.mk (λ J, @has_colimits.has_colimit_of_shape C _ c (discrete J) _)

/-- A cofan over `f : J → C` consists of a collection of maps from every `f j` to an object
    `CP`. This is enough to determine a cocone which factorizes through the coproduct. -/
@[hott]    
abbreviation cofan {J : Set} {C : Type _} [is_cat C] (f : J → C) := 
  cocone (discrete.functor f)

@[hott, hsimp]
def cofan.mk {J : Set} (C : Type _) [is_cat C] {f : J → C} {CP : C} 
  (p : Π j, f j ⟶ CP) : cofan f :=
cocone.mk CP (discrete.nat_trans p)

@[hott, hsimp] 
def copi.desc {J : Set} {C : Type _} [is_cat C] {f : J → C} [has_coproduct f]
  {CP : C} (p : Π j, f j ⟶ CP) : ⨿ f ⟶ CP :=
(get_colimit_cocone (discrete.functor f)).is_colimit.desc (cofan.mk _ p)  

@[hott, hsimp] 
def copi.π {J : Set} {C : Type u} [is_cat C] (f : J → C) [has_coproduct f] 
  (j : J) : f j ⟶ ⨿ f :=
(colimit.cocone (discrete.functor f)).π.app j 

@[hott]
def copi.hom_is_desc {J : Set} {C : Type _} [is_cat C] {f : J → C} 
  [has_coproduct f] {CP : C} (h : ⨿ f ⟶ CP) : h = copi.desc (λ j : J, (copi.π _ j) ≫ h) :=
let p := λ j : J, (copi.π f j) ≫ h, c := cofan.mk _ p,
    clc := get_colimit_cocone (discrete.functor f) in     
begin 
  change h = clc.is_colimit.desc c, 
  apply is_colimit.uniq clc.is_colimit c h, 
  intro j, exact rfl, 
end  

@[hott]
def copi.desc_π_eq {J : Set} (C : Type _) [is_cat C] {f : J → C} 
  [has_coproduct f] {CP : C} (p : Π j : J, f j ⟶ CP) : 
  ∀ j : J, (copi.π _ j) ≫ (copi.desc p) = p j :=
assume j, by apply is_colimit.fac  

@[hott]
def copi.desc_fac {J : Set} {C : Type _} [is_cat C] {f : J → C} 
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


/- The category of sets has all colimits. 

   The limit cocone is constructed as the quotient of the disjoint union of the sets in the 
   cocone base by the compatibility conditions of the indexing category. We define this 
   relation separately, for use later on.
   
   Note that the limit cocone vertex may be the empty set - then all cones over the functor `F`
   are empty because they cannot factorize through the empty set. -/
@[hott]
def colim_rep {J : Type _} [scJ : is_strict_cat J] (F : J ⥤ Set) : Set := 
  dprod_Set (Set.mk J scJ.set)  (λ j : J, F.obj j)

/- The relation is extended from the map compatibilities by symmetry and translativity. 
   Its inductive definition requires the outcome to be a type. For the quotient construction
   we turn it into a mere relation. -/
@[hott]
inductive set_colim_rel {J : Type u'} [scJ : is_strict_cat.{v'} J] (F : J ⥤ Set.{u}) : 
  colim_rep F -> colim_rep F -> Type (max u' v' u) 
| map : Π (j k : J) (h : j ⟶ k) (xj : F.obj j), set_colim_rel ⟨j,xj⟩ ⟨k, F.map h xj⟩ 
| symm : Π (x y : colim_rep F), set_colim_rel x y -> set_colim_rel y x
| trans : Π (x y z : colim_rep F) (q : set_colim_rel x y) (r : set_colim_rel y z), 
          set_colim_rel x z

@[hott]
def set_colim_mere_rel {J : Type u'} [scJ : is_strict_cat.{v'} J] (F : J ⥤ Set.{u}) : 
  colim_rep F -> colim_rep F -> trunctype -1 :=
assume x y, ∥set_colim_rel F x y∥

@[hott]
def set_colim_mere_rel.map {J : Type _} [scJ : is_strict_cat J] (F : J ⥤ Set) :
  Π (j k : J) (h : j ⟶ k) (xj : F.obj j), set_colim_mere_rel F ⟨j,xj⟩ ⟨k, F.map h xj⟩ :=
begin intros j k h xj, apply tr, constructor end

@[hott]
def set_colim_mere_rel.symm {J : Type _} [scJ : is_strict_cat J] (F : J ⥤ Set) :
  Π (x y : colim_rep F), set_colim_mere_rel F x y -> set_colim_mere_rel F y x :=
begin intros x y, apply trunc_functor, exact set_colim_rel.symm _ _ end

@[hott]
def set_colim_mere_rel.trans {J : Type _} [scJ : is_strict_cat J] (F : J ⥤ Set) :
  Π (x y z : colim_rep F) (q : set_colim_mere_rel F x y) (r : set_colim_mere_rel F y z), 
          set_colim_mere_rel F x z :=
begin intros x y z, apply trunc_functor2, exact set_colim_rel.trans _ _ _ end         

@[hott, reducible]
def set_cocone {J : Type _} [scJ : is_strict_cat J] (F : J ⥤ Set) : 
  cocone F :=
begin
  fapply cocone.mk,
  /- The limit cocone vertex set -/
  { exact set_quotient (set_colim_mere_rel F) },
  { fapply nat_trans.mk, 
    /- the leg maps of the limit cocone -/
    { intro j, exact λ f : F.obj j, set_class_of (set_colim_mere_rel F) ⟨j, f⟩ },
    /- compatibility of the leg maps -/
    { intros j k d, rwr constant_functor_map _ d, rwr is_precat.comp_id,
      apply eq_of_homotopy, intro f, 
      change set_class_of (set_colim_mere_rel F) ⟨k, F.map d f⟩ = 
             set_class_of (set_colim_mere_rel F) ⟨j, f⟩,
      apply eq_of_setrel, apply set_colim_mere_rel.symm, apply set_colim_mere_rel.map } }
  end 

@[hott, reducible]
def set_cocone_is_colimit {J : Type _} [is_strict_cat J] (F : J ⥤ Set) :
  is_colimit (set_cocone F) :=
begin 
  fapply is_colimit.mk,
  /- the descending to the colimit cocone from another cocone -/ 
  { intro s, intro x, fapply set_quotient.elim (set_colim_mere_rel F), 
    { exact λ fj : colim_rep F, s.π.app fj.1 fj.2 },
    { intros a a' Rmaa', hinduction Rmaa' with Raa', hinduction Raa', 
      { exact (homotopy_of_eq (s.π.naturality h) xj)⁻¹ }, 
      { exact ih⁻¹ },
      { exact ih_q ⬝ ih_r } },
    { exact x },
    { exact s.X.struct } },
  /- factorising the descending with colimit cocone legs -/    
  { intros s j, hsimp, apply eq_of_homotopy, 
    intro x, refl },
  /- uniqueness of descending -/  
  { intros s m desc_m, hsimp, apply eq_of_homotopy,
    intro x, fapply @set_quotient.rec _ (set_colim_mere_rel F) (λ x, m x = _), 
    { intro a, change m (set_class_of (set_colim_mere_rel F) a) = s.π.app a.1 a.2, 
      rwr <- homotopy_of_eq (desc_m a.1) a.2, 
      hinduction a, refl },
    { intros a a' H, apply pathover_of_tr_eq, exact is_set.elim _ _ } }  
end 

@[hott, reducible]
def set_colimit_cocone {J : Type _} [is_strict_cat J] (F : J ⥤ Set) : 
  colimit_cocone F :=
colimit_cocone.mk (set_cocone F) (set_cocone_is_colimit F)

@[hott, instance]
def set_has_colimit {J : Type _} [is_strict_cat J] (F : J ⥤ Set) : has_colimit F :=
  has_colimit.mk (set_colimit_cocone F)

@[hott, instance]
def set_has_colimits_of_shape {J : Type _} [is_strict_cat J] : 
  has_colimits_of_shape J Set :=
has_colimits_of_shape.mk (λ F, set_has_colimit F) 

/- Unions of subobjects of a given object in a category can be defined as colimits in the 
   category of such subobjects. Note that this is not the colimit in the surrounding 
   category but the image of the natural homomorphism to the containing object. Therefore,
   having colimits in the surrounding category is not enough for the existence of unions. 
   
   We also separately exhibit finite unions, for use in categorical models. -/
@[hott]
class has_union {C : Category} {c : C} {J : Set} (f : J -> subobject c) :=
  (exists_union : @has_coproduct _ subobject_is_cat _ f) 

@[hott, instance]
def has_union_to_has_coproduct {C : Category} {c : C} {J : Set} 
  (f : J -> subobject c) [H : has_union f] : has_coproduct f := H.exists_union

@[hott]
def subobject.union {C : Category} {c : C} {J : Set} (f : J -> subobject c)
  [has_union f] := ⨿ f

@[hott]
class has_unions {C : Category} (c : C) :=
  (has_union : Π {J : Set} (f : J -> subobject c), has_union f)

@[hott, instance]
def has_union_of_has_unions {C : Category} {c : C} [has_unions c] 
  {J : Set} (f : J -> subobject c) : has_union f :=
has_unions.has_union f 

@[hott]
def union_inc {C : Category} {c : C} {J : Set} (f : J -> subobject c)
  [has_union f] : Π j : J, f j ⟶ subobject.union f :=
assume j, copi.π f j

@[hott]
def union_fac {C : Category} {c : C} {J : Set} (f : J -> subobject c)
  [has_union f] {u : subobject c} (h : Π j, f j ⟶ u) : subobject.union f ⟶ u :=
copi.desc h    

@[hott]
class has_fin_union {C : Category} {c : C} {n : ℕ} 
  (f : fin_Set n -> subobject c) :=
(exists_union : has_union f)

@[hott, instance]
def has_union_of_has_fin_union {C : Category} {c : C} {n : ℕ} 
  (f : fin_Set n -> subobject c) [H : has_fin_union f] : has_union f :=
H.exists_union

@[hott]
class has_fin_unions (C : Category) :=
  (has_fin_union : Π (c : C) {n : ℕ} (f : fin_Set n -> subobject c), has_fin_union f)

@[hott, instance]
def has_fin_union_of_has_fin_unions {C : Category} [has_fin_unions C] {c : C} 
  {n : ℕ} (f : fin_Set n -> subobject c) : has_fin_union f :=
has_fin_unions.has_fin_union c f   

/- If finite unions exist every category of subobjects also has a bottom element, produced 
   as the empty union. -/
@[hott]
def bottom_subobject {C : Category} {c : C} [has_fin_unions C] : 
  subobject c :=
subobject.union (empty_fin_Set_map (subobject c))

@[hott] 
def bottom_subobj_prop {C : Category} {c : C} [has_fin_unions C] : 
  Π (a : subobject c), bottom_subobject ⟶ a :=
begin intro a, fapply union_fac, intro j, hinduction hott.nat.not_lt_zero j.1 j.2 end   

end categories.colimits

end hott