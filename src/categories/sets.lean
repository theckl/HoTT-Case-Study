import sets.subset categories.colimits categories.pullback categories.strict_cat

universes v v' u u' w
hott_theory

namespace hott
open hott.is_equiv hott.equiv hott.is_trunc hott.subset hott.precategories hott.categories 
     hott.categories.limits categories.adjoints hott.set hott.trunc 
     hott.categories.pullbacks hott.categories.colimits hott.categories.strict

namespace categories.sets

/- `Set.{u}` is a category - the category of `Type u`-small sets. -/
@[hott, instance]
def set_has_hom : has_hom Set.{u} :=
  has_hom.mk (λ A B : Set.{u}, Set.mk (A -> B) (@is_set_map A B))

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
   
   We first show that monomorphisms of sets are injective maps, and vice versa. -/
@[hott]
def mono_is_set_inj {A B : Set_Category} (f : A ⟶ B) : is_mono f -> is_set_injective f :=
begin  
  intro mon, intros a₁ a₂ feq,  
  let h₁ := hom_from_One a₁, let h₂ := hom_from_One a₂,
  have p : h₁ ≫ f = h₂ ≫ f, from 
    begin apply eq_of_homotopy, intro One.star, change f (h₁ _) = f (h₂ _), exact feq end,
  exact ap10 (mon One_Set h₁ h₂ p) One.star
end

@[hott]
def set_inj_is_mono {A B : Set_Category} (f : A ⟶ B) : is_set_injective f -> is_mono f :=
begin
  intro inj, intros C h₁ h₂ feq, apply eq_of_homotopy, intro c,  
  exact inj (h₁ c) (h₂ c) (ap10 feq c)
end

@[hott]
def bij_subobj_to_subset (A : Set_Category) : 
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
def subset_to_subobj {A : Set_Category} : Subset A -> subobject A :=
  λ B, (inv_bijection_of (bij_subobj_to_subset A)) B


@[hott]
def subset_to_subobj_eq {A : Set_Category} (B : Subset A) : 
  subset_to_subobj B = subobject.mk (pred_Set B) (pred_Set_map B)
                         (set_inj_is_mono (pred_Set_map B) (pred_Set_map_is_inj B)) :=
begin
  let p : bij_subobj_to_subset A = has_inverse_to_bijection _ _ _ := rfl, 
  change (inv_bijection_of (bij_subobj_to_subset A)).map B = _, rwr p
end 

@[hott]
def subset_is_subobj (A : Set_Category) : (Subobject.{u+1 u u} A) = (Powerset.{u} A) :=
begin 
  apply @bij_to_set_eq.{u+1 u} (@Subobject.{u+1 u u} Set_Category.{u} A) (Powerset A), 
  exact bij_subobj_to_subset A
end

/- The bijection between subsets and subobjects respects inclusions. -/
@[hott]
def inc_so_inc {A : Set_Category} : Π (B C : Subset A), B ⊆ C -> 
  subset_to_subobj B ≼ subset_to_subobj C :=
begin
  intros B C ss_inc, fapply hom_of_monos.mk,
  { rwr subset_to_subobj_eq, rwr subset_to_subobj_eq, hsimp,
    intro b, exact ⟨b.1, ss_inc b.1 b.2⟩ },
  { apply eq_of_homotopy, intro b, refl }
end

@[hott]
def so_inc_inc {A : Set_Category} : Π (B C : Subset A), 
  subset_to_subobj B ≼ subset_to_subobj C -> B ⊆ C :=
begin
  intros B C so_inc a B_inc, 
  have p : a = (so_inc.hom_obj ⟨a, B_inc⟩).1, from 
  begin change a = (so_inc.hom_obj ≫ (subset_to_subobj C).hom) ⟨a, B_inc⟩, rwr so_inc.fac end,
  rwr p, exact (so_inc.hom_obj ⟨a, B_inc⟩).2
end

/- The category of sets has all images. -/
@[hott]
def set_cat_image {A B : Set_Category} (f : A ⟶ B) : cat_image f :=
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
def set_has_image {A B : Set_Category} (f : A ⟶ B) : has_image f :=
  has_image.mk (tr (set_cat_image f)) 

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
def set_has_limits : has_limits Set_Category.{max u' u} :=
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
def One_Set_is_terminal : has_terminal Set_Category.{u} :=
begin
  apply has_terminal.mk, fapply terminal.mk, 
  { exact One_Set.{u} },
  { intro A, exact λ a : A.carrier, One.star  },
  { intros A f g, apply eq_of_homotopy, intro a, 
    exact @is_prop.elim _ (One_is_prop) _ _ }
end 


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


/-For constructions with sets, it is more efficient to use a simplified description of the 
   pullback than the one coming from the general limit construction of sets. -/
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
def pullback_to_set {A B C : Set} (f : A ⟶ C) (g : B ⟶ C) : 
  pullback f g -> pullback_set f g :=
begin 
  intro pb, fapply sigma.mk,
    exact (pb.1 (inf_w_node.tip ow_node.left), pb.1 (inf_w_node.tip ow_node.upper)),
    exact (pb.2 _ _ (inf_w_leg ow_node.left)) ⬝ (pb.2 _ _ (inf_w_leg ow_node.upper))⁻¹ 
end 

@[hott]
def set_to_pullback {A B C : Set} (f : A ⟶ C) (g : B ⟶ C) : 
  to_Set (Σ (ab : ↥A × ↥B), f ab.1 = g ab.2) -> pullback f g :=
pullback_lift (pb_set_square f g)
 

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


/- Using propositional resizing we can construct the subobject classifier for the 
   category of sets with `Prop` as the set of truth values. Since this set must be 
   in the category of sets, the propositions in `Prop` must be in a lower universe.
   Therefore, we only consider sets of `Type u+1` and must resize propositions.  -/
@[hott]
def set_true : terminal_obj ↥Set_Category.{u+1} ⟶ Prop_Set.{u} :=
  assume t, True

@[hott]
def subset_class_map {A : Set_Category.{u+1}} (B : subobject.{u+2 u+1} A) :
  A ⟶ Prop_Set.{u} :=
λ a, prop_resize.{u u+1} (a ∈ (bij_subobj_to_subset.{u+1 u+1} A) B) 

@[hott]
def subset_of_subset_class_map {A : Set_Category.{u+1}} (B : subobject.{u+2 u+1} A) :
  B = pullback_subobject (subset_class_map B) (term_subobj set_true) :=
begin
  fapply @subobj_antisymm.{u+2 u+1 u} Set_Category.{u+1} A B _, 
    { fapply pb_subobj_lift, 
      { exact terminal_map B.obj },
      { apply eq_of_homotopy, intro b, change subset_class_map B (B.hom b) = True,
        fapply inhabited_Prop_eq, 
        { apply prop_to_prop_resize, change ↥(image B.hom (B.hom b)), exact tr ⟨b, idp⟩ },
        { exact true.intro } } },
    { let f := subset_class_map B, let g := set_true, fapply hom_of_monos.mk,
      { intro pb,
        have p : subset_class_map B (pb.1 (inf_w_node.tip ow_node.left)) = True.{u}, from
          begin exact ap10.{u+1 u+1} (pullback_eq.{u+2 u+1} f g) pb end, 
        have im : ↥(image B.hom (pb.1 (inf_w_node.tip ow_node.left))), from 
        begin 
          apply prop_resize_to_prop.{u u+1}, 
          exact cast (ap trunctype.carrier p)⁻¹ true.intro.{u} 
        end,
        exact (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib B.hom 
                (mono_is_set_inj.{u+1 u} B.hom B.is_mono) 
                (pb.1 (inf_w_node.tip ow_node.left))) im).point },
      { apply eq_of_homotopy, intro pb, 
        let p : subset_class_map B (pb.1 (inf_w_node.tip ow_node.left)) = True.{u} :=
          begin exact ap10.{u+1 u+1} (pullback_eq.{u+2 u+1} f g) pb end, 
        let im : ↥(image B.hom (pb.1 (inf_w_node.tip ow_node.left))) := 
        begin 
          apply prop_resize_to_prop.{u u+1}, 
          exact cast (ap trunctype.carrier p)⁻¹ true.intro.{u} 
        end,
        change _ = pb.1 (inf_w_node.tip ow_node.left),
        let q := (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib B.hom 
                (mono_is_set_inj.{u+1 u} B.hom B.is_mono) 
                (pb.1 (inf_w_node.tip ow_node.left))) im).point_eq,
        rwr <- q } }
end

@[hott, instance]
def sets_have_so_classifier : has_so_classifier Set_Category.{u+1} :=
begin 
  apply has_so_classifier.mk, fapply subobject_classifier.mk,
  { exact Prop_Set.{u} }, 
  { exact set_true.{u} },
  { exact @subset_class_map },
  { intros A B, exact subset_of_subset_class_map B },
  { intros A B cl cart_cl, apply eq_of_homotopy, intro a, 
    change _ = prop_resize.{u u+1} (image B.hom a), 
    let T := terminal_obj.{u+1 u+2} Set_Category.{u+1},
    let g : ↥(T ⟶ Prop_Set.{u}) := λ (t : ↥T), True.{u},                      
    apply prop_iff_eq, 
    { intro p, apply prop_to_prop_resize, rwr cart_cl, 
      have H : cl a = (λ (t : (terminal_obj Set_Category.{u+1}).carrier), True.{u}) 
                          One.star, from inhabited_Prop_eq _ _ p true.intro,
      change ↥(image.{u+1 u+1} (pullback_homo_l.{u+2 u+1} cl g) a), 
      rwr set_pullback_homo_l_eq.{u+1} cl g, apply tr, fapply fiber.mk, 
      exact set_to_pullback.{u+1 u+1} cl g ⟨⟨a, One.star.{u+1}⟩, H⟩, 
      rwr pullback_to_set_rinv.{u+1 u+1} },
    { rwr cart_cl, intro p, let im := prop_resize_to_prop p,      
      let B' := pullback_subobject cl (term_subobj g),
      let fib_b' := (@untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib B'.hom 
                (mono_is_set_inj.{u+1 u} B'.hom B'.is_mono) a) im),
      rwr <- fib_b'.point_eq, 
      change (((pullback_homo_l _ _) ≫ cl) fib_b'.point).carrier,
      rwr pullback_eq, exact true.intro } }
end

@[hott]
def subset_to_class_map {A : Set_Category.{u+1}} (B : Subset A) :
  subset_class_map (subset_to_subobj.{u+1 u+1} B) = 
                                     λ a : A.carrier, prop_resize.{u u+1} (B a) :=
begin
  apply eq_of_homotopy, intro a,  
  apply ap prop_resize, 
  change (bij_subobj_to_subset.{u+1 u+1} A) 
                      ((inv_bijection_of (bij_subobj_to_subset.{u+1 u+1} A)) B) a = _,
  rwr inv_bij_r_inv (bij_subobj_to_subset.{u+1 u+1} A)
end

@[hott]
def ss_so_inter {A : Set_Category} {B C : Subset A} :
  subset_to_subobj (B ∩ C) = (subset_to_subobj B) ∩ (subset_to_subobj C) :=
begin             
  fapply subobj_antisymm,
  { apply subobj_inter_lift, exact inc_so_inc _ _ (inter_sset_l B C), 
                             exact inc_so_inc _ _ (inter_sset_r B C) },
  { let D := (subset_to_subobj B) ∩ (subset_to_subobj C), change D ≼ _,
    rwr <- inv_bij_l_inv (bij_subobj_to_subset A) D, apply inc_so_inc,
    have p : subset_to_subobj ((bij_subobj_to_subset A) D) =
          inv_bijection_of (bij_subobj_to_subset A) ((bij_subobj_to_subset A) D), from rfl,
    fapply inc_inc_inter_inc, 
    all_goals { apply so_inc_inc, rwr p, rwr inv_bij_l_inv (bij_subobj_to_subset A) D }, 
    exact subobj_inter_linc _ _ , exact subobj_inter_rinc _ _ }
end

@[hott]
def ss_so_union {A : Set_Category} {B C : Subset A} :
  subset_to_subobj (B ∪ C) = (subset_to_subobj B) ∪ (subset_to_subobj C) :=
begin             
  fapply subobj_antisymm,
  { sorry },
  { sorry }
end


end categories.sets

end hott