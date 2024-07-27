import sets.subset categories.basic

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc 
     hott.is_equiv hott.precategories hott.categories

/- We want to construct a category on a type `C` from a function from `C` to a
   category `X`, with a faithful functor to `X`. The additional data we need 
   for this purpose are a system of homomorphism that are subsets of the 
   homomorphisms between the image objects of `C`, the fact that the fibers of 
   `C -> X` are sets and that the precategory defined on `C` by the system of
   homomorphisms restricts to a category on the fibers. 
   
   The resulting category on `C`, with its faithful functor to `X`, is a 
   concrete category. The fibers provide a T-structure relative to `X` (see the
   entry `structured set` in [nLab]). -/
@[hott]
class concrete_hom_system {C : Type u} {X : Category.{u u}} (f : C -> X) :=
  (hom : Π c d : C, Subset (f c ⟶ f d))
  (id : ∀ c : C, 𝟙 (f c) ∈ hom c c)
  (comp : ∀ {c d e : C} {g : f c ⟶ f d} {h : f d ⟶ f e}, 
            (g ∈ hom c d) -> (h ∈ hom d e) -> g ≫ h ∈ hom c e)
  (inv : ∀ {c d : C} (g : f c ⟶ f d) (gih : is_iso g), (g ∈ hom c d) -> 
                                                               (gih.inv ∈ hom d c))

@[hott, instance]
def concrete_has_hom {C : Type u} {X : Category.{u u}} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : has_hom C :=
has_hom.mk (λ c d : C, pred_Set (concrete_hom_system.hom f c d)) 

@[hott]
def concrete_hom_eq_from_hom_eq {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] {c d : C} : 
  ∀ (g h : c ⟶ d), ((g.1 : f c ⟶ f d) = h.1) -> (g = h) :=
begin
  intros g h p, fapply sigma.sigma_eq, exact p,
  apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott, instance, hsimp]
def concrete_cat_struct {C : Type u} {X : Category.{u u}} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : category_struct C :=
category_struct.mk
  (λ a, ⟨𝟙 (f a), concrete_hom_system.id f a⟩)
  (λ c d e g h, ⟨g.1 ≫ h.1, concrete_hom_system.comp g.2 h.2⟩)

@[hott, instance, hsimp]
def concrete_is_precat {C : Type u} {X : Category.{u u}} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : is_precat C :=
begin
  fapply is_precat.mk,
    intros a b g, apply pred_Set_eq.{u u}, hsimp,
    intros a b g, apply pred_Set_eq.{u u}, hsimp,
    intros, apply pred_Set_eq.{u u}, hsimp
end 

@[hott]
def concrete_forget_functor {C : Type u} {X : Category.{u u}} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : C ⥤ X :=
begin 
  fapply precategories.functor.mk f,
  { intros c d g, exact g.1 },
  { intro c, exact idp },
  { intros c d e g h, exact idp }
end

@[hott, instance]
def concrete_fib_has_hom {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : Π (x : X), has_hom (fiber f x) :=
λ x, has_hom.mk (λ c d, to_Set (Σ (h : c.1 ⟶ d.1), (h.1 : f c.1 ⟶ f d.1) = 
                                       (idtoiso c.2).hom ≫ (idtoiso d.2⁻¹).hom))

@[hott]
def concrete_fib_hom_eq_from_concrete_hom_eq {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] {x : X} {c d : fiber f x} : 
  ∀ (g h : c ⟶ d), ((g.1 : c.1 ⟶ d.1) = h.1) -> (g = h) :=
begin
  intros g h p, fapply sigma.sigma_eq, exact p,
  apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott, instance]
def concrete_fib_cat_struct {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : Π (x : X), category_struct (fiber f x) :=
begin
  intro x, fapply category_struct.mk,
  { intro c, fapply dpair, exact 𝟙 c.1, 
    change 𝟙 (f c.1) = _, rwr idtoiso_comp_eq, rwr con.right_inv },
  { intros a b c g h, fapply dpair, exact g.1 ≫ h.1,
    have pg : g.1.1 = _, from g.2,
    have ph : h.1.1 = _, from h.2,
    change g.1.1 ≫ h.1.1 = _, rwr pg, rwr ph, 
    rwr is_precat.assoc (idtoiso a.point_eq).hom, 
    rwr <-is_precat.assoc (idtoiso b.point_eq⁻¹).hom,
    rwr idtoiso_comp_eq, rwr con.left_inv, rwr idtoiso_refl_eq, 
    change _ ≫ 𝟙 _ ≫ _ = _, rwr is_precat.id_comp }
end

--set_option trace.class_instances true

@[hott, instance]
def concrete_fib_is_precat {C : Type u} {X : Category.{u u}} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : Π (x : X), is_precat.{u u} (fiber f x) :=
begin
  intro x, fapply is_precat.mk,
  { intros c d g, fapply sigma.sigma_eq,
    { change 𝟙 c.1 ≫ g.1 = _, rwr @is_precat.id_comp _ _ c.1 d.1 g.1 },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { intros c d g, fapply sigma.sigma_eq,
    { change g.1 ≫ 𝟙 d.1 = _, rwr is_precat.comp_id },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { intros a b c d g h i, fapply sigma.sigma_eq,
    { change (g.1 ≫ h.1) ≫ i.1 = g.1 ≫ h.1 ≫ i.1, 
      rwr @is_precat.assoc _ (concrete_is_precat f) },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } 
end

/- Homomorphisms in `fiber f x` are automatically isomorphisms. -/
@[hott]
def concrete_fib_hom_inv {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] {x : X} {c d : fiber f x} : (c ⟶ d) -> (d ⟶ c) :=
begin
  intro g,
  fapply dpair, 
    { fapply dpair, 
      { fapply is_iso.inv, exact g.1.1, exact g.2⁻¹ ▸ (iso_comp_is_iso _ _) },
      { exact concrete_hom_system.inv g.1.1 _ g.1.2 } }, 
    { rwr id_inv_iso_inv, apply iso_move_rl, apply hott.eq.inverse, 
      apply iso_move_lr (iso.mk g.1.1 (g.2⁻¹ ▸ _)), 
      rwr <- iso_inv_inv (idtoiso d.point_eq), rwr <- id_inv_iso_inv, 
      change _ ≫ (idtoiso (d.point_eq)⁻¹).ih.inv = _,
      apply hott.eq.inverse, apply iso_move_rl, exact g.2⁻¹ }
end

@[hott]
def concrete_fib_hom_is_iso {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : ∀ {x : X} {c d : fiber f x} (g : c ⟶ d), 
  is_iso g :=
begin
  intros x c d g, fapply is_iso.mk, 
  { exact concrete_fib_hom_inv f g },
  { apply concrete_fib_hom_eq_from_concrete_hom_eq, change _ ≫ g.1 = 𝟙 d.1, 
    apply concrete_hom_eq_from_hom_eq, change _ ≫ g.1.1 = 𝟙 (f d.1), 
    exact (g.2⁻¹ ▸ (iso_comp_is_iso _ _)).r_inv },
  { apply concrete_fib_hom_eq_from_concrete_hom_eq, change g.1 ≫ _ = 𝟙 c.1, 
    apply concrete_hom_eq_from_hom_eq, change g.1.1 ≫ _ = 𝟙 (f c.1),
    exact (g.2⁻¹ ▸ (iso_comp_is_iso _ _)).l_inv }
end

/- We deduce that the precategory `C` over the category `X` is a category if the fibers
   over `X` are a category (which can be assumed as an instance). -/
@[hott]
class concrete_fibs_are_cat {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] :=
(ideqviso : ∀ (x : X) (c d : fiber f x), is_equiv (@idtoiso _ _ c d))

@[hott]
def concrete_fibcat_fib_isotoid {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] [concrete_fibs_are_cat f] :
  Π {x : X} {c d : fiber f x}, (c ≅ d) -> (c = d) :=
λ x c d, (concrete_fibs_are_cat.ideqviso x c d).inv

/- We construct `isotoid`  and `idtoiso` in several steps which we show to be invertible. -/
@[hott]
def concrete_iso_fib_iso {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : Π {c d : C}, (c ≅ d) -> 
  Σ (p : f c = f d), fiber.mk c p ≅ ⟨d, idp⟩ :=
begin
  intros c d i,
  fapply dpair,
  { exact category.isotoid (funct_iso_iso (concrete_forget_functor f) i) },
  { fapply iso.mk,
    { fapply dpair, exact i.hom, rwr idtoiso_comp_eq, rwr idp_inv, rwr con_idp, 
      rwr category.idtoiso_rinv' },
    { exact concrete_fib_hom_is_iso f _ } } 
end 

@[hott]
def concrete_fib_iso_iso {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] :  
  Π {c d : C}, (Σ (p : f c = f d), fiber.mk c p ≅ ⟨d, idp⟩) -> (c ≅ d) :=
begin
  intros c d pi, hinduction pi with p i_fib,
  fapply iso.mk,
  { exact i_fib.hom.1 },
  { fapply is_iso.mk,
    { exact i_fib.ih.inv.1 },
    { change (i_fib.ih.inv ≫ i_fib.hom).1 = _, rwr i_fib.ih.r_inv },
    { change (i_fib.hom ≫ i_fib.ih.inv).1 = _, rwr i_fib.ih.l_inv } }
end

@[hott]
def concrete_iso_fib_iso_rinv {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : Π {c d : C} (i : c ≅ d),
  concrete_fib_iso_iso f (concrete_iso_fib_iso f i) = i :=
begin
  intros c d i, apply hom_eq_to_iso_eq, exact idp
end

@[hott]
def concrete_fib_iso_fib_eq {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] [concrete_fibs_are_cat f] :  
  Π {c d : C}, (Σ (p : f c = f d), fiber.mk c p ≅ ⟨d, idp⟩) ->
               (Σ (p : f c = f d), fiber.mk c p = ⟨d, idp⟩) :=
begin
  intros c d pi, exact ⟨pi.1, concrete_fibcat_fib_isotoid f pi.2⟩
end

@[hott]
def concrete_fib_eq_fib_iso {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] :  
  Π {c d : C}, (Σ (p : f c = f d), fiber.mk c p = ⟨d, idp⟩) ->
               (Σ (p : f c = f d), fiber.mk c p ≅ ⟨d, idp⟩) :=
begin
  intros c d pi, exact ⟨pi.1, idtoiso pi.2⟩
end

@[hott]
def concrete_fib_iso_fib_eq_rinv {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] [concrete_fibs_are_cat f] :  
  Π {c d : C} (pi : Σ (p : f c = f d), fiber.mk c p ≅ ⟨d, idp⟩),
  concrete_fib_eq_fib_iso f (concrete_fib_iso_fib_eq f pi) = pi :=
begin
  intros c d pi, fapply sigma.sigma_eq, exact idp, 
  apply pathover_of_tr_eq, rwr idp_tr,
  apply (concrete_fibs_are_cat.ideqviso _ _ _).right_inv
end 

def concrete_fib_eq_eq {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] :  
  Π {c d : C}, (Σ (p : f c = f d), fiber.mk c p = ⟨d, idp⟩) -> (c = d) :=
λ c d pp, ap fiber.point pp.2 

def concrete_eq_fib_eq {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] :  
  Π {c d : C}, (c = d) -> (Σ (p : f c = f d), fiber.mk c p = ⟨d, idp⟩) :=
sorry

@[hott]
def concrete_fibcat_isotoid {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] [concrete_fibs_are_cat f] : 
  Π {c d : C}, (c ≅ d) -> (c = d) :=
begin
  intros c d i, 
  let p : f c = f d := category.isotoid (funct_iso_iso (concrete_forget_functor f) i),
  fapply @ap (fiber f (f d)) C fiber.point ⟨c,p⟩ ⟨d,idp⟩, apply concrete_fibcat_fib_isotoid f,
  fapply iso.mk,
  { fapply dpair, exact i.hom, rwr idtoiso_comp_eq, rwr idp_inv, rwr con_idp, 
    rwr category.idtoiso_rinv' },
  { fapply is_iso.mk,
    { fapply dpair, exact i.ih.inv, rwr idtoiso_comp_eq, rwr idp_con, rwr id_inv_iso_inv,
      rwr category.idtoiso_rinv' },
    { apply concrete_fib_hom_eq_from_concrete_hom_eq, exact i.ih.r_inv },
    { apply concrete_fib_hom_eq_from_concrete_hom_eq, exact i.ih.l_inv } }
end 

@[hott, instance]
def concrete_fib_cat_to_concrete_cat {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] [concrete_fibs_are_cat f] : 
  is_cat C :=
begin
  apply is_cat.mk , intros c d, fapply adjointify,
  { intro i, exact concrete_fibcat_isotoid f i },
  { intro i, apply hom_eq_to_iso_eq, apply concrete_hom_eq_from_hom_eq, sorry },
  { intro p, hinduction p, rwr idtoiso_refl_eq, sorry }
end

end hott