import sets.quotients categories.strict_cat categories.boolean

universes v v' u u' w
hott_theory

namespace hott
open hott.is_equiv hott.equiv hott.is_trunc hott.subset hott.precategories hott.categories 
     hott.categories.limits categories.adjoints hott.set hott.trunc 
     hott.categories.pullbacks hott.categories.colimits hott.categories.strict
     hott.categories.boolean

namespace categories.sets

/- `Set.{u}` is a category - the category of `Type u`-small sets. -/
@[hott, instance]
def set_has_hom : has_hom Set.{u} :=
  has_hom.mk (λ A B : Set.{u}, Set.mk (A -> B) (@is_set_map A B))

@[hott]
def to_hom_set {A B : Set.{u}} : (A -> B) -> (A ⟶ B) :=
  λ f, f 

@[hott, instance]
def set_cat_struct : category_struct Set.{u} :=
  category_struct.mk (λ A : Set.{u}, id_map A)
                     (λ (A B C: Set.{u}) (f : A ⟶ B) (g : B ⟶ C), g ∘ f)  

@[hott, instance]
def Set_is_precat : is_precat Set.{u} :=
  have ic : Π (A B : Set.{u}) (f : A ⟶ B), 𝟙 A ≫ f = f, from 
    assume A B f, by refl,
  have ci : Π (A B : Set.{u}) (f : A ⟶ B), f ≫ 𝟙 B = f, from 
    assume A B f, by refl,
  have as : Π (A B C D : Set.{u}) (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D),
             (f ≫ g) ≫ h = f ≫ (g ≫ h), from 
    assume A B C D f g h, by refl,
  is_precat.mk ic ci as

@[hott, hsimp]
def Set_isotocareqv {A B : Set.{u}} : (A ≅ B) -> (A ≃ B) :=
    assume i,
  have eqv_iso : is_equiv i.hom, from 
    have r_inv : ∀ b : B, i.hom (i.ih.inv b) = b, from 
      assume b, homotopy_of_eq i.ih.r_inv b,
    have l_inv : ∀ a : A, i.ih.inv (i.hom a) = a, from 
      assume a, homotopy_of_eq i.ih.l_inv a,
    adjointify i.hom i.ih.inv r_inv l_inv,
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
  ∀ a : A, (Set_isotoid i) ▸[λ A : Set.{u}, A.carrier] a = i.hom a :=
assume a,
have p : ((set_eq_to_car_eq (car_eq_to_set_eq (ua (Set_isotocareqv i))))) = 
         (ua (Set_isotocareqv i)), by 
    exact @is_equiv.right_inv _ _ _ 
           set_eq_equiv_car_eq.to_is_equiv (ua (Set_isotocareqv i)),
calc (Set_isotoid i) ▸ a = ((ap (trunctype.carrier) (Set_isotoid i)) ▸[λ A : Type u, A] a) : 
           (tr_ap (λ A : Type u, A) (trunctype.carrier) _ a)⁻¹
     ... = ((set_eq_to_car_eq (car_eq_to_set_eq (ua (Set_isotocareqv i)))) 
                                      ▸[λ A : Type u, A] a) : rfl      
     ... = ((ua (Set_isotocareqv i)) ▸[λ A : Type u, A] a) : 
           by rwr p
     ... = (equiv.equiv_of_eq (ua (Set_isotocareqv i))).to_fun a : cast_def _ _
     ... = i.hom a : cast_ua (Set_isotocareqv i) a

@[hott, hsimp]
def Set_isotoid_eq_refl {A : Set.{u}} : 
  Set_isotoid (id_iso A) = refl A :=
  calc Set_isotoid (id_iso A) = car_eq_to_set_eq (ua (equiv.refl ↥A)) : rfl
       ... = car_eq_to_set_eq (idpath ↥A) : by rwr ua_refl
       ... = refl A : car_idp_to_set_idp 

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
def Set_is_cat : is_cat Set.{u} :=
  have ideqviso : ∀ A B : Set.{u}, is_equiv (@idtoiso _ _ A B), from assume A B,
    adjointify idtoiso Set_isotoid Set_id_iso_rinv Set_id_iso_linv,
  is_cat.mk ideqviso  

@[hott]
def Set_Category : Category := Category.mk Set.{u} Set_is_cat

/- Homomorphisms from and to `One_Set`: `One_Set` is terminal inr the category of sets. -/
@[hott]
def hom_to_One (A : Set) : A ⟶ One_Set := λ a : A, One.star

@[hott]
def hom_to_One_is_unique {A : Set} : is_prop (A ⟶ One_Set) :=
begin
  apply is_prop.mk, intros f g, apply eq_of_homotopy, intro a, 
  exact @is_prop.elim _ One_is_prop _ _
end 

@[hott]
def hom_from_One {A : Set} (a : A) : One_Set ⟶ A := λ s : One_Set, a 


/- The categorical subobjects of a set in the category of sets are in bijections with 
   the subsets of the sets. 
   
   The bijection cannot directly be turned into an equality using univalence because 
   the two types live in different universes: Categorical subobjects contain sets 
   mapped into the given set, whereas subsets are defined as maps from the given set.
   `ulift` would allow the identification. 
   
   The definition of a subset in [sets.subset] actually uses the classifying map to a
   subobject classifier. These notions require the existence of pullbacks, so the proof 
   of this fact comes after the construction of pullbacks of sets. 

   We could use the subobject classifier to define intersections and unions for subsets
   given by classifying maps categorically, but since this makes dealing with subset
   algebra more difficult (and we do not yet see another use of the necessary 
   categorical developments), we keep the definitions in [sets.algebra] and show that 
   they are compatible with the bijection between subobjects of sets and subsets.
   
   We first show that monomorphisms of sets are injective maps, and vice versa. -/
@[hott]
def mono_is_set_inj {A B : Set.{u}} (f : A ⟶ B) : is_mono f -> is_set_injective f :=
begin  
  intro mon, intros a₁ a₂ feq,  
  let h₁ := hom_from_One a₁, let h₂ := hom_from_One a₂,
  have p : h₁ ≫ f = h₂ ≫ f, from 
    begin apply eq_of_homotopy, intro One.star, change f (h₁ _) = f (h₂ _), exact feq end,
  exact ap10 (mon One_Set h₁ h₂ p) One.star
end

@[hott]
def set_inj_is_mono {A B : Set.{u}} (f : A ⟶ B) : 
  is_set_injective f -> is_mono f :=
begin
  intro inj, intros C h₁ h₂ feq, apply eq_of_homotopy, intro c,  
  exact inj (h₁ c) (h₂ c) (ap10 feq c)
end

@[hott]
def bij_subobj_to_subset (A : Set.{u}) : 
  bijection (Subobject A) (Powerset A) :=
begin 
  fapply has_inverse_to_bijection,
  { intro B, exact inj_to_pred_sset (inj_Subset.mk B.obj B.hom 
                                                 (mono_is_set_inj B.hom B.is_mono)) },
  { intro B, fapply subobject.mk, exact pred_Set B, exact pred_Set_map B,
    exact set_inj_is_mono (pred_Set_map B) (pred_Set_map_is_inj B) },
  { fapply is_set_inverse_of.mk,
    { intro B, apply eq_of_homotopy, intro a, fapply prop_iff_eq, 
      { intro im, hinduction im with fib_a, rwr <- fib_a.point_eq, exact fib_a.point.2 },
      { intro P, apply tr, exact ⟨⟨a, P⟩, idp⟩ } },
    { intro B, fapply subobj_antisymm _ B, 
      { have H : Π a, is_prop (fiber B.hom a), from 
          begin 
            intro a, apply set_inj_implies_unique_fib, 
            exact mono_is_set_inj B.hom B.is_mono 
          end,
        fapply hom_of_monos.mk, 
        { intro el, exact (@trunc_equiv -1 (fiber B.hom el.1) (H el.1) el.2).1 },
        { hsimp, apply eq_of_homotopy, intro el, 
          exact (@trunc_equiv -1 (fiber B.hom el.fst) (H el.1) el.snd).point_eq } },
      { fapply hom_of_monos.mk,
        { intro b, fapply sigma.mk, exact B.hom b, exact tr ⟨b, idp⟩ },
        { hsimp, apply eq_of_homotopy, intro b, refl } } } } 
end

@[hott, reducible]
def subset_to_subobj {A : Set.{u}} : Subset A -> subobject A :=
  λ B, (inv_bijection_of (bij_subobj_to_subset A)) B


@[hott]
def subset_to_subobj_eq {A : Set.{u}} (B : Subset A) : 
  subset_to_subobj B = subobject.mk (pred_Set B) (pred_Set_map B)
                         (set_inj_is_mono (pred_Set_map B) (pred_Set_map_is_inj B)) :=
begin
  let p : bij_subobj_to_subset A = has_inverse_to_bijection _ _ _ := rfl, 
  change (inv_bijection_of (bij_subobj_to_subset A)).map B = _, rwr p
end 

@[hott]
def subset_is_subobj (A : Set.{u}) : (@Subobject Set.{u} _ A) = (Powerset A) :=
begin 
  apply @bij_to_set_eq.{u+1 u} (@Subobject Set.{u} _ A) (Powerset A), 
  exact bij_subobj_to_subset A
end

/- The bijection between subsets and subobjects respects inclusions. -/
@[hott]
def inc_so_inc {A : Set.{u}} : Π (B C : Subset A), B ⊆ C -> 
  subset_to_subobj B ≼ subset_to_subobj C :=
begin
  intros B C ss_inc, fapply hom_of_monos.mk,
  { rwr subset_to_subobj_eq, rwr subset_to_subobj_eq, hsimp,
    intro b, exact ⟨b.1, ss_inc b.1 b.2⟩ },
  { apply eq_of_homotopy, intro b, refl }
end

@[hott]
def so_inc_inc {A : Set.{u}} : Π (B C : Subset A), 
  subset_to_subobj B ≼ subset_to_subobj C -> B ⊆ C :=
begin
  intros B C so_inc a B_inc, 
  have p : a = (so_inc.hom_obj ⟨a, B_inc⟩).1, from 
  begin change a = (so_inc.hom_obj ≫ (subset_to_subobj C).hom) ⟨a, B_inc⟩, rwr so_inc.fac end,
  rwr p, exact (so_inc.hom_obj ⟨a, B_inc⟩).2
end

/- The category of sets has all images. -/
@[hott]
def set_cat_image {A B : Set.{u}} (f : A ⟶ B) : cat_image f :=
begin
  fapply cat_image.mk, 
  { exact subset_to_subobj (λ b : B.carrier, image f b) },
  { fapply sigma.mk, 
      intro a, exact ⟨f a, tr (fiber.mk a idp)⟩, 
      apply eq_of_homotopy, refl },
  { intros C C_im, 
    let im_imp : Π b : B.carrier, image f b -> image C.hom b := 
      begin 
        intro b, intro im_f, hinduction im_f, apply tr, fapply fiber.mk, exact C_im.1 a.point,
        change (C_im.fst ≫ C.hom) a.point = _, rwr (ap10 C_im.2 a.point), rwr a.point_eq 
      end,
    fapply hom_of_monos.mk,
    { intro b_im_f, 
      exact (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib C.hom 
            (mono_is_set_inj C.hom C.is_mono) b_im_f.1) (im_imp b_im_f.1 b_im_f.2)).point },
    { apply eq_of_homotopy, intro b_im_f, 
      
      let q := (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib C.hom 
          (mono_is_set_inj C.hom C.is_mono) b_im_f.1) (im_imp b_im_f.1 b_im_f.2)).point_eq,
      change C.hom _ = _, rwr q } }
end

@[hott, instance]
def set_has_image {A B : Set.{u}} (f : A ⟶ B) : has_image f :=
  has_image.mk (set_cat_image f) 

@[hott, instance]
def set_has_images : has_images Set.{u} :=
  has_images.mk (λ (A B : Set_Category) (f : A ⟶ B), set_has_image f)  

/- The category of sets has all limits. 

   The limit cone is constructed as the sections of the functor map satisfying the 
   compatibility conditions of the indexing category. We define this predicate separately, 
   for use later on.
   
   Note that the limit cone vertex may be the empty set - then all cones over the functor `F`
   are empty because otherwise they cannot factorize through the empty set. 
   
   Also note that the limit set must live in a universe both containing the diagram set 
   and the sets ordered according to the diagram, hence we must make sure that the 
   universes in which the diagram lives is not larger than the universe of sets, to 
   obtain a set in the correct universe. Most diagrams live in `Type 0`, so we do not 
   need to change the universe of sets for them. -/
@[hott]
def set_limit_pred {J : Type u'} [H : is_strict_cat.{u' u'} J] (F : J ⥤ Set.{max u' u}) : 
  Subset (@Sections (Set.mk J H.set) F.obj) :=
λ s, to_Prop (∀ (j k : J) (f : j ⟶ k), F.map f (s j) = s k) 

@[hott, reducible]
def set_cone {J : Type u'} [H : is_strict_cat.{u' u'} J] (F : J ⥤ Set.{max u' u}) : cone F :=
begin
  fapply cone.mk, 
  /- The limit cone vertex set -/
  { exact pred_Set (set_limit_pred F) }, 
  { fapply nat_trans.mk, 
    /- the leg maps of the limit cone -/
    { intro j, exact λ u, u.1 j },
    /- compatibility of the leg maps -/
    { intros j k f, hsimp, 
      fapply eq_of_homotopy, intro u, hsimp, change u.1 k = F.map f (u.1 j), 
      rwr u.2 j k f } }
end  

@[hott, reducible]
def set_cone_is_limit {J : Type u'} [H : is_strict_cat.{u' u'} J] (F : J ⥤ Set.{max u' u}) :
  is_limit (set_cone F) :=
begin 
  fapply is_limit.mk,
  { intro s, fapply cone_map.mk, 
    /- the lift from the limit cone to another cone-/ 
    { intro x, fapply sigma.mk, 
      { intro j, exact s.π.app j x },
      { hsimp, intros j k f, 
        exact (homotopy_of_eq (s.π.naturality f) x)⁻¹ } },
    /- factorising the lift with limit cone legs -/    
    { intro j, hsimp, apply eq_of_homotopy, 
      intro x, refl } },
  /- uniqueness of lift -/  
  { intros s m, hsimp, apply eq_of_homotopy,
    intro x, hsimp, fapply sigma.sigma_eq, 
    { exact eq_of_homotopy (λ j, @homotopy_of_eq s.X _ _ _ (m.fac j) x) },
    { hsimp, apply pathover_of_tr_eq, apply is_prop.elim } }  
end

@[hott, reducible]
def set_limit_cone {J : Type u'} [H : is_strict_cat.{u' u'} J] (F : J ⥤ Set.{max u' u}) : 
  limit_cone F := limit_cone.mk (set_cone F) (set_cone_is_limit F)

@[hott, instance]
def set_has_limit {J : Type u'} [H : is_strict_cat.{u' u'} J] (F : J ⥤ Set.{max u' u}) : 
  has_limit F := has_limit.mk (set_limit_cone F)

@[hott, instance]
def set_has_limits_of_shape {J : Type u'} [H : is_strict_cat.{u' u'} J] : 
  has_limits_of_shape J Set.{max u' u} := has_limits_of_shape.mk (λ F, set_has_limit F)     

@[hott, instance]
def set_has_limits : has_limits Set.{max u' u} :=
  has_limits.mk (λ {J : Type u'} [H : is_strict_cat.{u' u'} J], @set_has_limits_of_shape J H)

@[hott, instance]
def set_has_products : has_products Set.{max u' u} :=
  ⟨λ J : Set.{u'}, @set_has_limits_of_shape (discrete.{u'} J) _⟩

@[hott, instance]
def set_has_product {J : Set.{u'}} (f : J -> Set.{max u' u}) : has_product f :=
  ⟨set_has_limit (discrete.functor f)⟩

@[hott]
def Set_prod_sections {I : Set.{u'}} {U : I -> Set.{max u' u}} : (∏ U) = Sections U :=
begin
  change pred_Set (λ s : Sections U, set_limit_pred (discrete.functor U) s) = Sections U, 
  have pred_eq : (λ s : Sections U, set_limit_pred (discrete.functor U) s) = (λ s, True), from
    begin 
      apply eq_of_homotopy, intro s, hsimp, apply prop_iff_eq, 
      { intro p, exact true.intro },
      { intro t, intros j k f, 
        change (f ▸[λ k : discrete I, U j ⟶ U k] 𝟙 (U j)) (s j) = s k, 
        hinduction f, rwr idp_tr } 
    end,
  rwr pred_eq, apply car_eq_to_set_eq, 
  apply ap trunctype.carrier (total_pred_Set_eq_Set.{u' (max u' u)} (Sections U))
end 


/- The category of sets has `One_Set` as terminal object. -/
@[hott, instance]
def One_Set_is_terminal : terminal Set.{u} :=
begin
  fapply terminal.mk, 
  { exact One_Set.{u} },
  { intro A, exact λ a : A.carrier, One.star  },
  { intros A f g, apply eq_of_homotopy, intro a, 
    exact @is_prop.elim _ (One_is_prop) _ _ }
end 

@[hott]
def term_Set : Set := One_Set_is_terminal.term_obj

@[hott]
def term_Set_map (A : Set) : A ⟶ term_Set := terminal.term_map A

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
def set_cocone {J : Type u'} [scJ : is_strict_cat.{u' u'} J] (F : J ⥤ Set.{max u' u}) : 
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
def set_cocone_is_colimit {J : Type u'} [is_strict_cat.{u' u'} J] (F : J ⥤ Set.{max u' u}) :
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
def set_colimit_cocone {J : Type u'} [is_strict_cat.{u' u'} J] (F : J ⥤ Set.{max u' u}) : 
  colimit_cocone F :=
colimit_cocone.mk (set_cocone F) (set_cocone_is_colimit F)

@[hott, instance]
def set_has_colimit {J : Type u'} [is_strict_cat.{u' u'} J] (F : J ⥤ Set.{max u' u}) : 
  has_colimit F := has_colimit.mk (set_colimit_cocone F)

@[hott, instance]
def set_has_colimits_of_shape {J : Type u'} [is_strict_cat.{u' u'} J] : 
  has_colimits_of_shape J Set.{max u' u} :=
has_colimits_of_shape.mk (λ F, set_has_colimit F) 

@[hott, instance]
def set_has_colimits : has_colimits Set.{max u' u} :=
begin 
  apply has_colimits.mk, intros J strict, exact @set_has_colimits_of_shape J strict 
end

/- From the existence of colimits and hence coproducts and images follows the existence 
   of unions. -/
@[hott, instance]
def set_has_unions : has_unions Set.{max u' u} :=
begin 
  apply has_unions.mk, intros A J f, 
  exact has_subobj_union_of_has_coproducts_and_images f 
end 

/- For constructions with sets, it is more efficient to use a simplified description of 
   coproducts than the one coming from the general colimit construction of sets. -/
@[hott]
def coproduct_set {J : Set.{u'}} (f : J -> Set.{max u' u}) :=
  to_Set (Σ (j : J), f j)

@[hott]
def copr_set_pi {J : Set.{u'}} (f : J -> Set.{max u' u}) :  
  Π j : J, f j ⟶ coproduct_set f :=
assume j fj, ⟨j, fj⟩ 

@[hott]
def copi_to_set {J : Set.{u'}} (f : J -> Set.{max u' u}) :
  (⨿ f) -> coproduct_set f :=
copi.desc (copr_set_pi f) 

@[hott]
def set_to_copi {J : Set.{u'}} (f : J -> Set.{max u' u}) :
  coproduct_set f -> ⨿ f :=
begin 
  intro cpf, 
  let copi_pi : f cpf.1 -> ⨿ f := copi.π f cpf.1,
  exact copi_pi cpf.2 
end

/- For constructions with sets, it is more efficient to use a simplified description of the 
   pullback than the one coming from the general limit construction of sets. The same 
   applies to pullbacks of subsets. -/
@[hott]
def pullback_set {A B C : Set} (f : A ⟶ C) (g : B ⟶ C) := 
  to_Set (Σ (ab : ↥A × ↥B), f ab.1 = g ab.2)

@[hott]
def pb_set_l {A B C : Set} (f : A ⟶ C) (g : B ⟶ C) : pullback_set f g ⟶ A :=
  λ pb', pb'.1.1

@[hott]
def pb_set_t {A B C : Set} (f : A ⟶ C) (g : B ⟶ C) : pullback_set f g ⟶ B :=
  λ pb', pb'.1.2

@[hott]
def pb_set_eq {A B C : Set} (f : A ⟶ C) (g : B ⟶ C) : 
  pb_set_l f g ≫ f = pb_set_t f g ≫ g := 
begin apply eq_of_homotopy, intro pb', exact pb'.2 end 

@[hott]
def pb_set_square {A B C : Set} (f : A ⟶ C) (g : B ⟶ C) : square f g :=
  square.of_i_j (pb_set_eq f g)

@[hott]
def pullback_to_set {A B C : Set.{u}} (f : A ⟶ C) (g : B ⟶ C) : 
  pullback f g -> pullback_set f g :=
begin 
  intro pb, fapply sigma.mk,
    exact (pb.1 (inf_w_node.tip ow_node.left), pb.1 (inf_w_node.tip ow_node.upper)),
    exact (pb.2 _ _ (inf_w_leg ow_node.left)) ⬝ (pb.2 _ _ (inf_w_leg ow_node.upper))⁻¹ 
end 

@[hott]
def set_to_pullback {A B C : Set.{u}} (f : A ⟶ C) (g : B ⟶ C) : 
  to_Set (Σ (ab : ↥A × ↥B), f ab.1 = g ab.2) -> pullback f g :=
pullback_lift (pb_set_square.{u u} f g)
 

@[hott]
def pullback_to_set_rinv {A B C : Set} (f : A ⟶ C) (g : B ⟶ C) :
  Π (pb' : Σ (ab : ↥A × ↥B), f ab.1 = g ab.2), 
  pullback_to_set f g (set_to_pullback f g pb') = pb' :=
begin 
  intro pb', let pb := pullback_lift (pb_set_square f g) pb',
  fapply sigma.sigma_eq, 
  { fapply pair_eq, 
    { change pb.1 (inf_w_node.tip ow_node.left) = square_left (pb_set_square f g) pb', 
      rwr <- pb_lift_eq_l,
      have p : (pullback_lift (pb_set_square f g) ≫ pullback_homo_l f g) pb' = 
               pullback_homo_l f g pb, from rfl,
      rwr p },
    { change pb.1 (inf_w_node.tip ow_node.upper) = square_top (pb_set_square f g) pb', 
      rwr <- pb_lift_eq_t,
      have q : (pullback_lift (pb_set_square f g) ≫ pullback_homo_t f g) pb' = 
               pullback_homo_t f g pb, from rfl,
      rwr q } },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott]
def set_pullback_homo_l_eq {A B C : Set} (f : A ⟶ C) (g : B ⟶ C) : 
  pullback_homo_l f g = λ pb : pullback f g, (pullback_to_set f g pb).1.1 :=
rfl

@[hott]
def pb_subobj_set {A B : Set.{u}} (f : A ⟶ B) (D : Subobject B) : Subobject A :=
  subset_to_subobj (λ a, f a ∈ (bij_subobj_to_subset B) D)

@[hott]
def pb_subobj_set_eq {A B : Set.{u}} (D : Subobject B) (f : A ⟶ B) :
  pb_subobj_set f D = pullback_subobject f D :=
begin
  rwr <- inv_bij_l_inv (bij_subobj_to_subset A) (pullback_subobject f D),
  apply ap subset_to_subobj, apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc₁, 
    let d := (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib D.hom 
            (mono_is_set_inj D.hom D.is_mono) (f a)) inc₁).point,
    let p := (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib D.hom 
            (mono_is_set_inj D.hom D.is_mono) (f a)) inc₁).point_eq,
    change ↥(image (pullback_homo_l f D.hom) a), rwr set_pullback_homo_l_eq, 
    apply tr, fapply fiber.mk, 
    { apply set_to_pullback.{u} f D.hom, exact ⟨(a,d), p⁻¹⟩ },
    { rwr pullback_to_set_rinv.{u u} } },
  { intros a inc₂, 
    let fd := (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib _ 
            (mono_is_set_inj _ (mono_is_stable f D.hom D.is_mono)) a) inc₂).point,
    let p := (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib _ 
            (mono_is_set_inj _ (mono_is_stable f D.hom D.is_mono)) a) inc₂).point_eq,
    apply tr, fapply fiber.mk, 
    { exact (pullback_to_set _ _ fd).1.2 },
    { rwr <- p, exact eq.inverse (pullback_to_set _ _ fd).2 } }
end 

/- Images are stable under pullbacks in the category of sets. -/
@[hott, instance]
def set_has_stable_images : has_stable_images Set.{u} :=
begin
  apply has_stable_images.mk,
  intros A B C f g, fapply subobj_antisymm,
  { rwr <- pb_subobj_set_eq, apply inc_so_inc, 
    intros a inc₁, 
    change ↥((bij_subobj_to_subset C).map (subset_to_subobj 
                                                   (λ (b : C.carrier), image g b)) _), 
    have p : subset_to_subobj (λ (b : C.carrier), image g b) = (inv_bijection_of 
               (bij_subobj_to_subset C)).map (λ (b : C.carrier), image g b), from idp,
    rwr p, rwr inv_bij_r_inv, hinduction inc₁ with fa, apply tr, fapply fiber.mk,
    exact pullback_homo_t f g fa.point, 
    change (pullback_homo_t f g ≫ g) fa.point = _, rwr <- pullback_eq, 
    change f _ = _, rwr fa.point_eq },
  { rwr <- pb_subobj_set_eq, apply inc_so_inc, 
    intros a inc₂, change ↥((bij_subobj_to_subset C).map (subset_to_subobj _) (f a)) at inc₂, 
    have p : subset_to_subobj (λ (b : C.carrier), image g b) = (inv_bijection_of 
               (bij_subobj_to_subset C)).map (λ (b : C.carrier), image g b), from idp,
    rwr p at inc₂, rwr inv_bij_r_inv at inc₂, hinduction inc₂ with gfa, apply tr, fapply fiber.mk,
    exact set_to_pullback _ _ ⟨(a,gfa.point), gfa.point_eq⁻¹⟩, 
    rwr set_pullback_homo_l_eq }
end


/- Using propositional resizing we can construct the subobject classifier for the 
   category of sets with `Prop` as the set of truth values. Since this set must be 
   in the category of sets, the propositions in `Prop` must be in a lower universe.
   Therefore, we only consider sets of `Type u+1` and must resize propositions.  -/
@[hott]
def set_true : term_Set.{u+1} ⟶ Prop_Set.{u} :=
  assume t, True

@[hott]
def subset_class_map {A : Set.{u+1}} (B : subobject A) :
  A ⟶ Prop_Set.{u} :=
λ a, prop_resize.{u u+1} (a ∈ (bij_subobj_to_subset A) B) 

@[hott]
def subset_of_subset_class_map {A : Set.{u+1}} (B : subobject A) :
  B = pullback_subobject (subset_class_map B) (term_subobj _ set_true) :=
begin
  fapply @subobj_antisymm Set.{u+1} _ A B _, 
    { fapply pb_subobj_lift, 
      { exact term_Set_map B.obj },
      { apply eq_of_homotopy, intro b, change subset_class_map B (B.hom b) = True,
        fapply inhabited_Prop_eq, 
        { apply prop_to_prop_resize, change ↥(image B.hom (B.hom b)), exact tr ⟨b, idp⟩ },
        { exact true.intro } } },
    { let f := subset_class_map B, let g := set_true, fapply hom_of_monos.mk,
      { intro pb,
        have p : subset_class_map B (pb.1 (inf_w_node.tip ow_node.left)) = True.{u}, from
          begin exact ap10 (pullback_eq f g) pb end, 
        have im : ↥(image B.hom (pb.1 (inf_w_node.tip ow_node.left))), from 
        begin 
          apply prop_resize_to_prop.{u u+1}, 
          exact cast (ap trunctype.carrier p)⁻¹ true.intro.{u} 
        end,
        exact (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib B.hom 
                (mono_is_set_inj B.hom B.is_mono) 
                (pb.1 (inf_w_node.tip ow_node.left))) im).point },
      { apply eq_of_homotopy, intro pb, 
        let p : subset_class_map B (pb.1 (inf_w_node.tip ow_node.left)) = True.{u} :=
          begin exact ap10 (pullback_eq f g) pb end, 
        let im : ↥(image B.hom (pb.1 (inf_w_node.tip ow_node.left))) := 
        begin 
          apply prop_resize_to_prop.{u u+1}, 
          exact cast (ap trunctype.carrier p)⁻¹ true.intro.{u} 
        end,
        change _ = pb.1 (inf_w_node.tip ow_node.left),
        let q := (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib B.hom 
                (mono_is_set_inj B.hom B.is_mono) 
                (pb.1 (inf_w_node.tip ow_node.left))) im).point_eq,
        rwr <- q } }
end

@[hott, instance]
def sets_have_so_classifier : has_so_classifier Set.{u+1} :=
begin 
  apply has_so_classifier.mk, fapply subobject_classifier.mk,
  { exact Prop_Set.{u} }, 
  { exact set_true.{u} },
  { exact @subset_class_map },
  { intros A B, exact subset_of_subset_class_map B },
  { intros A B cl cart_cl, apply eq_of_homotopy, intro a, 
    change _ = prop_resize.{u u+1} (image B.hom a), 
    let T := term_Set.{u+1},
    let g : ↥(T ⟶ Prop_Set.{u}) := λ (t : ↥T), True.{u},                      
    apply prop_iff_eq, 
    { intro p, apply prop_to_prop_resize, rwr cart_cl, 
      have H : cl a = (λ (t : (term_Set.{u+1}).carrier), True.{u}) 
                          One.star, from inhabited_Prop_eq _ _ p true.intro,
      change ↥(image.{u+1 u+1} (pullback_homo_l.{u+2 u+1} cl g) a), 
      rwr set_pullback_homo_l_eq.{u+1} cl g, apply tr, fapply fiber.mk, 
      exact set_to_pullback.{u+1} cl g ⟨⟨a, One.star.{u+1}⟩, H⟩, 
      rwr pullback_to_set_rinv.{u+1 u+1} },
    { rwr cart_cl, intro p, let im := prop_resize_to_prop p,      
      let B' := pullback_subobject cl (term_subobj _ g),
      let fib_b' := (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib B'.hom 
                (mono_is_set_inj B'.hom B'.is_mono) a) im),
      rwr <- fib_b'.point_eq, 
      change (((pullback_homo_l _ _) ≫ cl) fib_b'.point).carrier,
      rwr pullback_eq, exact true.intro } }
end

@[hott]
def subset_to_class_map {A : Set.{u+1}} (B : Subset A) :
  subset_class_map (subset_to_subobj B) = 
                                     λ a : A.carrier, prop_resize.{u u+1} (B a) :=
begin
  apply eq_of_homotopy, intro a,  
  apply ap prop_resize, 
  change (bij_subobj_to_subset A).map 
                      ((inv_bijection_of (bij_subobj_to_subset A)).map B) a = _,
  rwr inv_bij_r_inv (bij_subobj_to_subset A)
end

@[hott]
def ss_so_inter {A : Set} {B C : Subset A} :
  subset_to_subobj (B ∩ C) = (subset_to_subobj B) ∩ (subset_to_subobj C) :=
begin             
  fapply subobj_antisymm,
  { apply subobj_inter_lift, exact inc_so_inc _ _ (inter_sset_l B C), 
                             exact inc_so_inc _ _ (inter_sset_r B C) },
  { let D := (subset_to_subobj B) ∩ (subset_to_subobj C), change D ≼ _,
    rwr <- inv_bij_l_inv (bij_subobj_to_subset A) D, apply inc_so_inc,
    have p : subset_to_subobj ((bij_subobj_to_subset A).map D) =
          (inv_bijection_of (bij_subobj_to_subset A)).map ((bij_subobj_to_subset A).map D), from rfl,
    fapply inc_inc_inter_inc, 
    all_goals { apply so_inc_inc, rwr p, rwr inv_bij_l_inv (bij_subobj_to_subset A) D }, 
    exact subobj_inter_linc _ _ , exact subobj_inter_rinc _ _ }
end

@[hott]
def ss_so_union {A : Set.{u}} {B C : Subset A} :
  subset_to_subobj (B ∪ C) = (subset_to_subobj B) ∪ (subset_to_subobj C) :=
begin             
  fapply subobj_antisymm,
  { let D := (subset_to_subobj B) ∪ (subset_to_subobj C), change _ ≼ D, 
    rwr <- inv_bij_l_inv (bij_subobj_to_subset A) D, apply inc_so_inc,
    have p : subset_to_subobj ((bij_subobj_to_subset A).map D) =
          (inv_bijection_of (bij_subobj_to_subset A)).map ((bij_subobj_to_subset A).map D), from rfl,
    fapply inc_inc_union_inc, 
    all_goals { apply so_inc_inc, rwr p, rwr inv_bij_l_inv (bij_subobj_to_subset A) D }, 
    exact subobj_union_linc _ _ , exact subobj_union_rinc _ _ },
  { apply lift_to_union, exact inc_so_inc _ _ (union_sset_l B C), 
                             exact inc_so_inc _ _ (union_sset_r B C) }
end

@[hott]
def ss_so_iunion {A : Set.{max u' u}} {J : Set.{u'}} (f : J -> Subset A) : 
  subset_to_subobj (iUnion f) = subobject.union (λ j : J, subset_to_subobj (f j)) :=
begin
  fapply subobj_antisymm,
  { rwr <- inv_bij_l_inv (bij_subobj_to_subset A) 
                         (subobject.union (λ j : J, subset_to_subobj (f j))),
    apply inc_so_inc, apply iUnion_sset, intros j a inc₁, 
    change ↥(image (subobject.union (λ j : J, subset_to_subobj (f j))).hom a),
    apply tr, fapply fiber.mk, 
    { exact (union_inc (λ j : J, subset_to_subobj (f j)) j).hom_obj ⟨a, inc₁⟩ }, 
    { refl } },
  { apply union_fac (λ j : J, subset_to_subobj (f j)), intro j,
    apply inc_so_inc, exact sset_iUnion f j }
end

@[hott]
def so_union_ss {A : Set.{max u' u}} {J : Set.{u'}} (f : J -> Subobject A) :
  Subset A := (bij_subobj_to_subset A) (subobject.union f)

@[hott]
def so_iunion_ss {A : Set.{max u' u}} {J : Set.{u'}} (f : J -> Subobject A) :
  Subset A := iUnion (λ j : J, (bij_subobj_to_subset A) (f j))  

@[hott]
def so_ss_iunion {A : Set.{max u' u}} {J : Set.{u'}} (f : J -> Subobject A) :
  so_union_ss f = so_iunion_ss f :=
begin
  rwr <- inv_bij_r_inv (bij_subobj_to_subset A) (so_iunion_ss f),
  apply ap (bij_subobj_to_subset A), change _ = subset_to_subobj (so_iunion_ss f),
  let f' := λ j : J, (bij_subobj_to_subset A) (f j),
  have p : f = λ j : J, subset_to_subobj (f' j), from 
    begin 
      apply eq_of_homotopy, intro j, hsimp, 
      change _ = (inv_bijection_of (bij_subobj_to_subset A)).map 
                                                    ((bij_subobj_to_subset A).map (f j)),
      rwr inv_bij_l_inv (bij_subobj_to_subset A) (f j) 
    end,
  rwr p, rwr <- ss_so_iunion f', apply ap subset_to_subobj, apply ap iUnion,
  hsimp, apply eq_of_homotopy, intro j, hsimp,
  change _ = (bij_subobj_to_subset A).map ((inv_bijection_of (bij_subobj_to_subset A)).map 
                                                     (f' j)),
  rwr inv_bij_r_inv (bij_subobj_to_subset A) (f' j)
end

@[hott]
def so_iunion_of_comp {A : Set.{max u' u}} {J : Set.{u'}} (f : J -> Subobject A) : 
  Π a : A.carrier, image (subobject.union f).hom a -> ∥Σ j : J, image (f j).hom a∥ :=
begin
  intros a sou_im, 
  change ↥(a ∈ so_union_ss f) at sou_im, rwr so_ss_iunion at sou_im, 
  hinduction prop_resize_to_prop sou_im with eq comp, hinduction comp with i fi,
  hinduction fi with fib,
  apply tr, fapply sigma.mk, exact i, apply tr, fapply fib
end

@[hott]
def ss_so_top {A : Set.{u}} : 
  subset_to_subobj (total_Subset A) = top_subobject A :=
begin             
  fapply subobj_antisymm,
  { exact top_subobj_prop _ },
  { fapply hom_of_monos.mk, 
    { intro a, exact ⟨a, true.intro⟩ }, 
    { exact idp } }
end

@[hott]
def ss_so_bottom {A : Set.{u}} : 
  subset_to_subobj (empty_Subset A) = bottom_subobject A :=
begin             
  fapply subobj_antisymm,
  { fapply hom_of_monos.mk,
    { intro a, hinduction a.2 },
    { apply eq_of_homotopy, intro a, hinduction a.2 } },
  { exact bottom_subobj_prop _ }
end

@[hott]
def set_compl_of {A : Set.{u}} [H : has_dec_elem A] (B : subobject A) : 
  complement B :=
begin
  fapply complement.mk,
  { exact subset_to_subobj 𝒞((bij_subobj_to_subset A).map B) }, 
  { rwr <- inv_bij_l_inv (bij_subobj_to_subset A) B,
    change subset_to_subobj _ ∪ _ = _, rwr <- ss_so_union, 
    rwr compl_union_top ((bij_subobj_to_subset A).map B), rwr ss_so_top }, 
  { rwr <- inv_bij_l_inv (bij_subobj_to_subset A) B,
    change subset_to_subobj _ ∩ _ = _, rwr <- ss_so_inter, 
    rwr compl_inter_bottom, rwr ss_so_bottom }
end

@[hott, instance]
def subobj_has_complements {A : Set.{u}} [H : has_dec_elem A] : 
  @has_complement (subobject A) :=
has_complement.mk (λ B, (set_compl_of B).na)

@[hott, instance]
def set_has_stable_unions : has_stable_unions Set.{max u' u} :=
begin
  apply has_stable_unions.mk, intros A B f J i,
  change _ = subobject.union (λ j : J, pullback_subobject f (i j)),
  rwr <- pb_subobj_set_eq, 
  have p : (λ j : J, pullback_subobject f (i j)) = 
           (λ j : J, pb_subobj_set f (i j)), from 
    begin apply eq_of_homotopy, intro j, hsimp, rwr pb_subobj_set_eq end,
  rwr p, change subset_to_subobj _ = subobject.union (λ j : J, subset_to_subobj _), 
  rwr <- ss_so_iunion, apply ap subset_to_subobj, fapply subset_asymm, 
  { intros a' inc, hinduction so_iunion_of_comp i (f a') inc with eq comp,
    fapply sset_iUnion, exact comp.1, exact comp.2 },
  { apply iUnion_sset, intros j a',
    change ((bij_subobj_to_subset B) (i j) (f a')) -> 
                       ((bij_subobj_to_subset B) (subobject.union i) (f a')), 
    intro inc, hinduction inc with fa, apply tr, fapply fiber.mk, 
    exact (union_inc i j).hom_obj fa.point,
    change ((union_inc i j).hom_obj ≫ (subobject.union i).hom) fa.point = _, 
    rwr (union_inc i j).fac, exact fa.point_eq }
end

@[hott, instance]
def set_has_complements [H : Π A : Set, has_dec_elem A] : 
  has_complements Set :=
begin apply has_complements.mk, intro A, exact set_compl_of end

/- The category of sets has an all-of-fiber functor. -/
@[hott]
def set_all_fib {A B : Set} (f : A ⟶ B) : subobject A ⥤ subobject B :=
begin
  fapply precategories.functor.mk, 
    { intro D, 
      exact subset_to_subobj (λ b : B.carrier, 
                   to_Prop (∀ a : A.carrier, f a = b -> image D.hom a)) },
    { intros C D h, fapply hom_of_monos.mk, 
      { intro elC, fapply sigma.mk, exact elC.1, intros a eq,  
        hinduction elC.2 a eq with eq' fib_C, apply tr, fapply fiber.mk,
        exact h.hom_obj fib_C.point, change (h.hom_obj ≫ D.hom) _ = _, rwr h.fac, 
        exact fib_C.point_eq },
      { apply eq_of_homotopy, intro elC, refl } },
    { intro C, exact is_prop.elim _ _ },
    { intros C D E g h, exact is_prop.elim _ _ }
end

@[hott, instance]
def set_has_all_of_fibers : has_all_of_fibers Set :=
begin  
  apply has_all_of_fibers.mk, intros A B f, apply has_all_of_fiber.mk, 
  apply has_right_adjoint.mk, fapply is_left_adjoint.mk, 
  { exact set_all_fib f },
  { apply adjoint_hom_to_adjoint, fapply adjoint_functors_on_hom.mk,
    { intros C D, fapply bijection_of_props, 
      { change (pullback_subobject f C ≼ D) -> (C ≼ _), rwr <- pb_subobj_set_eq,
        intro g, rwr <- inv_bij_l_inv (bij_subobj_to_subset A) D at g,
        let g' := so_inc_inc _ _ g,
        rwr <- inv_bij_l_inv (bij_subobj_to_subset B) C, apply inc_so_inc, 
        intros b inc₁ a eq, rwr <- eq at inc₁, exact g' a inc₁ },
      { change (C ≼ _) -> (pullback_subobject f C ≼ D), rwr <- pb_subobj_set_eq,
        intro h, rwr <- inv_bij_l_inv (bij_subobj_to_subset B) C at h,
        let h' := so_inc_inc _ _ h,
        rwr <- inv_bij_l_inv (bij_subobj_to_subset A) D, apply inc_so_inc,
        intros a inc₂, exact h' (f a) inc₂ a rfl } },
    { intros C D C' h g, exact is_prop.elim _ _ },
    { intros C D D' g h, exact is_prop.elim _ _ } }
end

@[hott, instance] 
def set_cat_is_Cartesian : is_Cartesian Set.{max u' u} :=
begin fapply is_Cartesian.mk, apply_instance end

@[hott, instance] 
def set_cat_is_regular : is_regular Set.{max u' u} :=
begin fapply is_regular.mk, apply_instance end

@[hott, instance] 
def set_cat_is_coherent : is_coherent Set.{max u' u} :=
begin fapply is_coherent.mk, apply_instance end

@[hott, instance]
def set_cat_is_Heyting : is_Heyting Set.{max u' u} :=
begin fapply @is_Heyting.mk Set, apply_instance end

@[hott]
def set_cat_is_Boolean [H : Π A : Set, has_dec_elem A] : 
  is_Boolean Set.{max u' u} :=
begin fapply is_Boolean.mk, exact set_has_complements end

end categories.sets

end hott