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
class concrete_hom_system {C : Type u} {X : Category.{u' v}} (f : C -> X) :=
  (hom : Π c d : C, Subset (f c ⟶ f d))
  (id : ∀ c : C, 𝟙 (f c) ∈ hom c c)
  (comp : ∀ {c d e : C} {g : f c ⟶ f d} {h : f d ⟶ f e}, 
            (g ∈ hom c d) -> (h ∈ hom d e) -> g ≫ h ∈ hom c e)
  (inv : ∀ {c d : C} (g : f c ⟶ f d) (gih : is_iso g), (g ∈ hom c d) -> 
                                                               (gih.inv ∈ hom d c))

@[hott, instance]
def concrete_has_hom {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : has_hom C :=
has_hom.mk (λ c d : C, pred_Set (concrete_hom_system.hom f c d)) 

@[hott]
def concrete_hom_eq_from_hom_eq {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] {c d : C} : 
  ∀ (g h : c ⟶ d), ((g.1 : f c ⟶ f d) = h.1) -> (g = h) :=
begin
  intros g h p, fapply sigma.sigma_eq, exact p,
  apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott, instance, hsimp]
def concrete_cat_struct {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : category_struct C :=
category_struct.mk
  (λ a, ⟨𝟙 (f a), concrete_hom_system.id f a⟩)
  (λ c d e g h, ⟨g.1 ≫ h.1, concrete_hom_system.comp g.2 h.2⟩)

@[hott, instance, hsimp]
def concrete_is_precat {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : is_precat C :=
begin
  fapply is_precat.mk,
  { intros a b g, apply pred_Set_eq, hsimp },
  { intros a b g, apply pred_Set_eq, hsimp },
  { intros, apply pred_Set_eq, hsimp }
end 

@[hott]
def concrete_forget_functor {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : C ⥤ X :=
begin 
  fapply precategories.functor.mk f,
  { intros c d g, exact g.1 },
  { intro c, exact idp },
  { intros c d e g h, exact idp }
end

@[hott]
def concrete_forget_functor_is_faithful {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : is_faithful_functor (concrete_forget_functor f) :=
begin
  intros x y g₁ g₂, intro g_eq, fapply sigma.sigma_eq, 
  { exact g_eq },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end

/- Fibers of the map from a concrete type to the underlying category inherit a 
   precategory structure. -/
@[hott, instance]
def concrete_fib_has_hom {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : Π (x : X), has_hom (fiber f x) :=
λ x, has_hom.mk (λ c d, to_Set (Σ (h : c.1 ⟶ d.1), (h.1 : f c.1 ⟶ f d.1) = 
                                       (idtoiso c.2).hom ≫ (idtoiso d.2⁻¹).hom))

@[hott]
def concrete_fib_hom_eq_from_concrete_hom_eq {C : Type u} {X : Category.{u' v}} 
  {f : C -> X} [concrete_hom_system f] {x : X} {c d : fiber f x} : 
  ∀ (g h : c ⟶ d), ((g.1 : c.1 ⟶ d.1) = h.1) -> (g = h) :=
begin
  intros g h p, fapply sigma.sigma_eq, exact p,
  apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott, instance]
def concrete_fib_cat_struct {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : Π (x : X), category_struct (fiber f x) :=
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

@[hott, instance]
def concrete_fib_is_precat {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : Π (x : X), is_precat (fiber f x) :=
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

@[hott, reducible]
def concrete_fib_functor {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : Π (x : X), (fiber f x) ⥤ X :=
begin
  intro x, fapply precategories.functor.mk,
  { intro c, exact f c.1 },
  { intros c d g, exact g.1.1 },
  { intro c, exact idp },
  { intros c d e g h, exact idp }
end

/- Homomorphisms in `fiber f x` are uniquely determined by source and target, and they 
   are automatically isomorphisms. -/
@[hott]
def concrete_fib_hom_is_unique {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] {x : X} {c d : fiber f x} : ∀ (g h : c ⟶ d), g = h :=
begin
  intros g h, apply concrete_fib_hom_eq_from_concrete_hom_eq,
  apply concrete_hom_eq_from_hom_eq,
  have pg : g.1.1 = _, from g.2,
  have ph : h.1.1 = _, from h.2,
  rwr pg, rwr ph
end 

@[hott, instance]
def concrete_fib_hom_is_prop {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] {x : X} {c d : fiber f x} : is_prop (c ⟶ d) :=
is_prop.mk (λ g h, concrete_fib_hom_is_unique g h)

@[hott]
def concrete_fib_hom_inv {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] {x : X} {c d : fiber f x} : (c ⟶ d) -> (d ⟶ c) :=
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
def concrete_fib_hom_is_iso {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] : ∀ {x : X} {c d : fiber f x} (g : c ⟶ d), 
  is_iso g :=
begin
  intros x c d g, fapply is_iso.mk, 
  { exact concrete_fib_hom_inv g },
  { apply concrete_fib_hom_is_unique },
  { apply concrete_fib_hom_is_unique }
end

@[hott]
def concrete_fib_hom_to_iso {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] : ∀ {x : X} {c d : fiber f x} (g : c ⟶ d), 
  f c.1 ≅ f d.1 :=
λ x c d g, funct_iso_iso (concrete_fib_functor f x) (iso.mk g (concrete_fib_hom_is_iso g))

/- We deduce that the precategory `C` over the category `X` is a category if the fibers
   over `X` are a category. An instance of this property can be deduced from more basic 
   assumptions. 
   
   If the fibers are categories, they are also sets. -/
@[hott]
class concrete_fibs_are_cat {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] :=
(homtoid : ∀ {x : X} {c d : fiber f x}, (c ⟶ d) -> (c = d))
(idhom_to_idp : ∀ {x : X} (c : fiber f x), homtoid (𝟙 c) = idp)

@[hott, instance]
def concrete_fibs_cat {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] [concrete_fibs_are_cat f] :
  Π (x : X), is_cat (fiber f x) :=
begin 
  intro x, fapply is_cat.mk, intros c d, fapply adjointify, 
  { intro g, exact concrete_fibs_are_cat.homtoid g.hom },
  { intro i, apply hom_eq_to_iso_eq, apply concrete_fib_hom_is_unique },
  { intro p, hinduction p, apply concrete_fibs_are_cat.idhom_to_idp }
end 

@[hott]
def concrete_fibcat_fib_isotoid {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] [concrete_fibs_are_cat f] :
  Π {x : X} {c d : fiber f x}, (c ≅ d) -> (c = d) :=
λ x c d, (is_cat.ideqviso c d).inv

@[hott]
def concrete_fibcat_fib_id_iso_to_idp {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] [concrete_fibs_are_cat f] :
  Π {x : X} (c : fiber f x), concrete_fibcat_fib_isotoid (id_iso c) = idp :=
begin
  intros x c, rwr <- idtoiso_refl_eq, change idtoiso⁻¹ᶠ _ = _,
  rwr @is_equiv.left_inv _ _ idtoiso (is_cat.ideqviso c c) idp
end

@[hott]
class concrete_fibs_are_set {C : Type u} {X : Category.{u' v}} (f : C -> X) :=
  (set : ∀ (x : X), is_set (fiber f x))

@[hott, instance]
def concrete_fibset_set {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_fibs_are_set f] : Π {x : X}, is_set (fiber f x) :=
λ x, concrete_fibs_are_set.set f x  

@[hott, instance]
def concrete_fibs_cat_are_set {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] [concrete_fibs_are_cat f] : concrete_fibs_are_set f :=
begin
  apply concrete_fibs_are_set.mk, intro x, apply is_trunc_succ_intro, 
  intros c d, 
  apply is_trunc_equiv_closed_rev -1 
          (@category.ideqviso (Category.mk (fiber f x) (concrete_fibs_cat f x)) c d), 
  apply is_prop.mk, intros i j, apply hom_eq_to_iso_eq, 
  apply concrete_fib_hom_is_unique
end

/- We construct `isotoid`  and `idtoiso` in several steps which we show to be invertible. -/
@[hott]
def concrete_iso_fib_iso {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] : Π {c d : C}, (c ≅ d) -> 
  Σ (p : f c = f d), fiber.mk c p ≅ ⟨d, idp⟩ :=
begin
  intros c d i,
  fapply dpair,
  { exact category.isotoid (funct_iso_iso (concrete_forget_functor f) i) },
  { fapply iso.mk,
    { fapply dpair, exact i.hom, rwr idtoiso_comp_eq, rwr idp_inv, rwr con_idp, 
      rwr category.idtoiso_rinv' },
    { exact concrete_fib_hom_is_iso _ } } 
end 

def concrete_id_iso_fib_id_iso {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] [concrete_fibs_are_cat f] : 
  Π {c : C}, concrete_iso_fib_iso (id_iso c) = dpair idp (id_iso _) :=
begin
  intro c, 
  fapply sigma.sigma_eq, 
  { change category.isotoid _ = _, rwr funct_id_iso_id_iso, 
     rwr isotoid_id_refl ((concrete_forget_functor f).obj c) }, 
  { apply pathover_of_tr_eq,
    have H : Π (x : X) (c d : fiber f x), is_prop (c ≅ d), from 
    begin 
      intros x c d, 
      exact @cat_set_eq_is_prop (fiber f x) _ _ c d 
    end,   
    exact @is_prop.elim _ (H _ _ _) _ _ }
end   

@[hott]
def concrete_fib_iso_iso {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] :  
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
def concrete_fib_id_iso_id_iso {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] :  
  Π {c : C}, concrete_fib_iso_iso (dpair (@idp _ (f c)) (id_iso _)) = id_iso c :=
λ c, hom_eq_to_iso_eq idp   

@[hott]
def concrete_iso_fib_iso_rinv {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [hom_sys : concrete_hom_system f] : Π {c d : C} (i : c ≅ d),
  concrete_fib_iso_iso (concrete_iso_fib_iso i) = i :=
begin
  intros c d i, apply hom_eq_to_iso_eq, exact idp
end

@[hott]
def concrete_fib_iso_fib_eq {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] [concrete_fibs_are_cat f] :  
  Π {c d : C}, (Σ (p : f c = f d), fiber.mk c p ≅ ⟨d, idp⟩) ->
               (Σ (p : f c = f d), fiber.mk c p = ⟨d, idp⟩) :=
begin
  intros c d pi, exact ⟨pi.1, concrete_fibcat_fib_isotoid pi.2⟩
end

@[hott]
def concrete_fib_eq_fib_iso {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [hom_sys : concrete_hom_system f] :  
  Π {c d : C}, (Σ (p : f c = f d), fiber.mk c p = ⟨d, idp⟩) ->
               (Σ (p : f c = f d), fiber.mk c p ≅ ⟨d, idp⟩) :=
begin
  intros c d pi, exact ⟨pi.1, idtoiso pi.2⟩
end

@[hott]
def concrete_fib_idp_fib_id_iso {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] : 
  Π {c : C}, concrete_fib_eq_fib_iso (dpair (@idp _ (f c)) idp) = 
             ⟨@idp _ (f c), id_iso _⟩ :=
λ c, idp

@[hott]
def concrete_fib_id_iso_fib_idp {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] [concrete_fibs_are_cat f] : 
  Π {c : C}, concrete_fib_iso_fib_eq ⟨@idp _ (f c), id_iso _⟩ =
              (dpair (@idp _ (f c)) idp):=
begin 
  intro c, fapply sigma.sigma_eq,
  { exact idp },
  { apply pathover_of_tr_eq, rwr idp_tr, 
    change concrete_fibcat_fib_isotoid (id_iso _) = _,
    rwr concrete_fibcat_fib_id_iso_to_idp } 
end

@[hott]
def concrete_fib_iso_fib_eq_rinv {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] [concrete_fibs_are_cat f] :  
  Π {c d : C} (pi : Σ (p : f c = f d), fiber.mk c p ≅ ⟨d, idp⟩),
  concrete_fib_eq_fib_iso (concrete_fib_iso_fib_eq pi) = pi :=
begin
  intros c d pi, fapply sigma.sigma_eq, exact idp, 
  apply pathover_of_tr_eq, rwr idp_tr,
  apply (is_cat.ideqviso _ _).right_inv
end 

@[hott, hsimp]
def concrete_fib_eq_eq {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] :  
  Π {c d : C}, (Σ (p : f c = f d), fiber.mk c p = ⟨d, idp⟩) -> (c = d) :=
λ c d pp, ap fiber.point pp.2 

@[hott, hsimp]
def concrete_eq_fib_eq {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] :  
  Π {c d : C}, (c = d) -> (Σ (p : f c = f d), fiber.mk c p = ⟨d, idp⟩) :=
begin
  intros c d p, fapply dpair, exact ap f p, fapply apd011 fiber.mk, exact p,
  hinduction p, rwr ap_idp
end

@[hott]
def concrete_fib_eq_eq_rinv {C : Type u} {X : Category.{u' v}} {f : C -> X} 
  [concrete_hom_system f] [concrete_fibs_are_set f] :  
  Π {c d : C} (pp : Σ (p : f c = f d), fiber.mk c p = ⟨d, idp⟩),
    concrete_eq_fib_eq f (concrete_fib_eq_eq pp) = pp :=
begin
  intros c d pp, hinduction pp with pf p_fib, hsimp,
  fapply sigma.sigma_eq, 
  { change ap f _ = pf, rwr fiber_ap_ap },
  { apply pathover_of_tr_eq, exact is_set.elim _ _ }
end

@[hott, hsimp]
def concrete_fibcat_idtoiso {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] [concrete_fibs_are_cat f] : 
  Π {c d : C}, (c = d) -> (c ≅ d) :=
λ c d i, concrete_fib_iso_iso (concrete_fib_eq_fib_iso (concrete_eq_fib_eq f i))

@[hott]
def concrete_fibcat_idtoiso_eq {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] [concrete_fibs_are_cat f] : 
  Π {c d : C} (p : c = d), idtoiso p = concrete_fibcat_idtoiso f p :=
begin
  intros c d p, hinduction p, rwr idtoiso_refl_eq, hsimp, 
  change id_iso _ = concrete_fib_iso_iso (concrete_fib_eq_fib_iso (dpair idp idp)),
  rwr concrete_fib_idp_fib_id_iso, rwr concrete_fib_id_iso_id_iso
end 

@[hott]
def concrete_fibcat_isotoid {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] [concrete_fibs_are_cat f] : 
  Π {c d : C}, (c ≅ d) -> (c = d) :=
λ c d i, concrete_fib_eq_eq (concrete_fib_iso_fib_eq (concrete_iso_fib_iso i)) 

@[hott, instance]
def concrete_fib_cat_to_concrete_cat {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [concrete_hom_system f] [concrete_fibs_are_cat f] : 
  is_cat C :=
begin
  fapply is_cat.mk, intros c d, fapply adjointify,
  { intro i, exact concrete_fibcat_isotoid f i },
  { intro i, rwr concrete_fibcat_idtoiso_eq f,
    change concrete_fib_iso_iso (concrete_fib_eq_fib_iso (concrete_eq_fib_eq f
                                                        (concrete_fib_eq_eq _))) = _,                                                    
    rwr concrete_fib_eq_eq_rinv _, rwr concrete_fib_iso_fib_eq_rinv, 
    rwr concrete_iso_fib_iso_rinv, apply_instance },
  { intro p, hinduction p, rwr idtoiso_refl_eq, 
    change concrete_fib_eq_eq.{v u} _ = _, rwr concrete_id_iso_fib_id_iso f, 
    rwr concrete_fib_id_iso_fib_idp f } 
end 

/- If the map from a concrete type to the underlying category is injective and all the 
   homomorphisms between underlying objects are homomorphisms of the objects of a concrete 
   type, then the concrete type is a category. In that case, the concrete type is actually
   a full subcategory of the underlying category, as in [categories.subcat], but we also
   want to use it in the framework of concrete categories. -/
@[hott, reducible, instance]
def full_subcat_hom_sys {C : Type u} {X : Category.{u' v}} (f : C -> X) [is_injective f] : 
  concrete_hom_system f :=
concrete_hom_system.mk (λ c d, total_Subset (f c ⟶ f d)) (λ c, true.intro) 
                       (λ c d e g h g_el h_el, true.intro) (λ c d g gih g_el, true.intro)

@[hott, instance]
def full_subcat_fibs_is_singleton {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [inj : is_injective f] : Π (x : X), is_prop (fiber f x) :=
begin
  intro x, apply is_prop.mk, intros c d, fapply fiber.fiber_eq,
    { fapply inj_imp inj, exact c.point_eq ⬝ d.point_eq⁻¹ },
    { change _ = ap f (@is_equiv.inv _ _ (λ p : c.point = d.point, ap f p) 
               (@is_injective.eqv _ _ _ inj _ _) 
               (c.point_eq ⬝ (d.point_eq)⁻¹)) ⬝ _,
      have q : ap f (@is_equiv.inv _ _ (λ p : c.point = d.point, ap f p) 
              (@is_injective.eqv _ _ _ inj _ _) 
               (c.point_eq ⬝ (d.point_eq)⁻¹)) = (c.point_eq ⬝ (d.point_eq)⁻¹), from
        @is_equiv.right_inv _ _ _ (@is_injective.eqv _ _ _ inj c.1 d.1) _, 
      rwr q, rwr con.assoc, rwr con.left_inv }
end

@[hott,instance]
def full_subcat_fibs_are_cat {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [inj : is_injective f] : concrete_fibs_are_cat f :=
begin 
  fapply concrete_fibs_are_cat.mk, 
  { intros x c d g, exact is_prop.elim c d },
  { intros x c, exact is_set.elim _ _ }
end

@[hott, instance]
def full_subcat_is_cat {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  [inj : is_injective f] : is_cat C :=
concrete_fib_cat_to_concrete_cat f

/- We can also show that a type over a category has the structure of a concrete category
   if we can characterize the fibers of the forgetful map as a category with only one 
   element in each homomorphism set. -/
@[hott]
class fib_hom_system {X : Category.{v+1 u}} (B : X -> Type u) :=
  (set : Π (x : X), is_set (B x))
  (hom : Π {x : X}, B x -> B x -> Set.{v})
  (unique : Π {x : X} (c d : B x), is_prop (hom c d))

@[hott, instance]
def fib_has_hom {X : Category.{v+1 u}} (B : X -> Type u) 
  [H : fib_hom_system B] (x : X) : has_hom (B x) :=
has_hom.mk (λ c d : B x, (fib_hom_system.hom X c d)) 

/- Equivalences between a type over a category `X` and a type dependent on `X`. -/
@[hott]
class concrete_sigma_system {C : Type (u+1)} {X : Category.{v+1 u}} (f : C -> X)
  [concrete_hom_system f] (B : X -> Type u) [fib_hom_system B] :=
(fib_eqv : Π {x : X}, B x ≃ fiber f x) 
(hom_eqv : Π {x : X} (c d : B x), (c ⟶ d) ≃ ((fib_eqv.to_fun c) ⟶ (fib_eqv.to_fun d)))

@[hott, instance]
def concrete_sigma_sys_fib_set {C : Type (u+1)} {X : Category.{v+1 u}} (f : C -> X)
  [concrete_hom_system f] (B : X -> Type u) [H_fib : fib_hom_system B] 
  [H_sig : concrete_sigma_system f B] : Π (x : X), is_set (fiber f x) :=
begin 
  intro x, 
  apply is_trunc_equiv_closed 0 (@concrete_sigma_system.fib_eqv _ _ f _ B _ _ x), 
  exact fib_hom_system.set B x
end

@[hott]
class sigma_fibs_are_cat {X : Category.{v+1 u}} (B : X -> Type u) [fib_hom_system B] :=
  (homtoid : ∀ {x : X} {b₁ b₂ : B x}, (b₁ ⟶ b₂) -> b₁ = b₂)

@[hott, instance]
def concrete_type_with_fib_sys_has_fib_cat {C : Type (u+1)} {X : Category.{v+1 u}} 
  (f : C -> X) (B : X -> Type u) [fib_hom_system B] [concrete_hom_system f] 
  [H_fB : concrete_sigma_system f B] [H_S : sigma_fibs_are_cat B] : 
  concrete_fibs_are_cat f :=
begin
  fapply concrete_fibs_are_cat.mk,
  { intros x c d, 
    rwr <- @is_equiv.right_inv _ _ _ (@concrete_sigma_system.fib_eqv _ _ 
                                                               f _ B _ _ x).to_is_equiv c,
    rwr <- @is_equiv.right_inv _ _ _ (@concrete_sigma_system.fib_eqv _ _ 
                                                               f _ B _ _ x).to_is_equiv d,
    intro g, apply λ p, ap (concrete_sigma_system.fib_eqv f B).to_fun p, apply H_S.homtoid, 
    exact @is_equiv.inv _ _ _ (@concrete_sigma_system.hom_eqv _ _ 
                                                      f _ B _ _ x _ _).to_is_equiv g }, 
  { intros x c, exact is_set.elim _ _ }
end

@[hott, instance]
def concrete_type_with_fib_sys_is_cat {C : Type (u+1)} {X : Category.{v+1 u}} 
  (f : C -> X) (B : X -> Type u) [H_obj : fib_hom_system B] 
  [H_hom : concrete_hom_system f] [concrete_sigma_system f B] [sigma_fibs_are_cat B] : 
is_cat C := by apply_instance

end hott