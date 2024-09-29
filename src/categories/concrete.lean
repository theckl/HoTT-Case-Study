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
  is_cat.{v u} C :=
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
@[hott, instance]
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

/- A Sigma-type over a category with a homomorphism system is a concrete category with
   respect to the first projection if the induced precategory on each of the dependent 
   types are categories. This follows as above, and the deduction cannot be cut short, as 
   every type mapping to a category is equivalent to the family of the fibers over the 
   category, and fibers of the first projection on a family of types are equivalent to the
   dependent type [hott.types.fiber.fiber_pr1], hence their identity types are also 
   equivalent [hott.init.equiv.eq_equiv_fn_eq_fn]. 
   
   However, fibers of maps are awkward to manipulate, so some of the properties needed to 
   deduce the category property are more easily constructed when the dependent types in a
   family have a more accessible description than just as fibers of the first projection. 
  
   We first introduce homomorphisms and precategory isomorphisms between concrete types 
   over an underlying category, that is those concrete categories whose forgetful functors 
   are full. -/
@[hott]
structure concrete_equiv {C₁ C₂ : Type _} {X : Category.{u' v}} (f₁ : C₁ -> X) 
  (f₂ : C₂ -> X) :=
(eqv : C₁ ≃ C₂)
(comm_hom : Π c₁ : C₁, f₁ c₁ = f₂ (eqv c₁)) 

@[hott]
def concrete_equiv_inv {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} {f₂ : C₂ -> X} : 
  (concrete_equiv f₁ f₂) -> (concrete_equiv f₂ f₁) := 
begin
  intro c_eqv, fapply concrete_equiv.mk,
  { exact equiv.symm c_eqv.eqv },
  { intro c₂, change _ = f₁ (c_eqv.eqv⁻¹ᵉ.to_fun _), 
    rwr equiv.to_fun_symm, revert c₂, apply homotopy_inv_of_homotopy_pre, intro c₂, 
    rwr c_eqv.comm_hom c₂ }
end 

/- The following checks that the underlying homomorphisms of two equivalent concrete 
   categories are in bijection and that the bijection respects identity, composition,
   isomorphisms and inverse maps, may seem long-winded and a figment of HoTT. However, 
   there is an unavoidable core to the calculations: Since the objects of the underlying 
   category do not need to form a set (for example, if they are sets), equalities as 
   prescribed by the concrete equivalence are not uniquely determined. -/
@[hott] 
def concrete_full_hom_equiv {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} (c_eqv : concrete_equiv f₁ f₂) : Π {c₁ d₁ : C₁}, 
  bijection (f₁ c₁ ⟶ f₁ d₁) (f₂ (c_eqv.eqv c₁) ⟶ f₂ (c_eqv.eqv d₁)) :=
begin
  intros c₁ d₁, fapply has_inverse_to_bijection,
  { intro g₁, exact (idtoiso (c_eqv.comm_hom c₁)).ih.inv ≫ g₁ ≫
                    (idtoiso (c_eqv.comm_hom d₁)).hom },
  { intro g₂, exact (idtoiso (c_eqv.comm_hom c₁)).hom ≫ g₂ ≫
                    (idtoiso (c_eqv.comm_hom d₁)).ih.inv },
  { fapply is_set_inverse_of.mk, 
    { intro g₂, change _ ≫ (_ ≫ _ ≫ _) ≫ _ = g₂,
      rwr <- is_precat.assoc (idtoiso (c_eqv.comm_hom c₁)).ih.inv _ _, 
      rwr <- is_precat.assoc (idtoiso (c_eqv.comm_hom c₁)).ih.inv _ _,
      rwr is_iso.r_inv, rwr is_precat.id_comp, rwr is_precat.assoc, rwr is_iso.r_inv,
      rwr is_precat.comp_id },
    { intro g₁, change _ ≫ (_ ≫ _ ≫ _) ≫ _ = g₁,
      rwr <- is_precat.assoc (idtoiso (c_eqv.comm_hom c₁)).hom _ _, 
      rwr <- is_precat.assoc (idtoiso (c_eqv.comm_hom c₁)).hom _ _,
      rwr is_iso.l_inv, rwr is_precat.id_comp, rwr is_precat.assoc, rwr is_iso.l_inv,
      rwr is_precat.comp_id } }
end

@[hott]
def concrete_full_hom_equiv_id {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} (c_eqv : concrete_equiv f₁ f₂) : Π (c₁ : C₁),
  (concrete_full_hom_equiv c_eqv).map (𝟙 (f₁ c₁)) = 𝟙 (f₂ (c_eqv.eqv c₁)) :=
begin 
  intro c₁, change _ ≫ _ ≫ _ = _, rwr is_precat.id_comp, rwr is_iso.r_inv
end

@[hott]
def concrete_full_hom_equiv_comp {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} (c_eqv : concrete_equiv f₁ f₂) : Π {c₁ d₁ e₁ : C₁} (g : f₁ c₁ ⟶ f₁ d₁)
  (h : f₁ d₁ ⟶ f₁ e₁), (concrete_full_hom_equiv c_eqv).map (g ≫ h) =
  (concrete_full_hom_equiv c_eqv).map g ≫ (concrete_full_hom_equiv c_eqv).map h :=
begin
  intros c₁ d₁ e₁ g h, change _ ≫ _ ≫ _ = (_ ≫ _ ≫ _) ≫ (_ ≫ _ ≫ _), 
  rwr is_precat.assoc _ (g ≫ _) _, rwr is_precat.assoc g (idtoiso _).hom, 
  rwr <- is_precat.assoc ((idtoiso (c_eqv.comm_hom d₁)).hom), rwr is_iso.l_inv,
  rwr is_precat.id_comp, rwr <- is_precat.assoc g h
end

@[hott]
def concrete_full_hom_equiv_iso {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} (c_eqv : concrete_equiv f₁ f₂) : Π {c₁ d₁ : C₁} {g : f₁ c₁ ⟶ f₁ d₁},
  is_iso g -> is_iso ((concrete_full_hom_equiv c_eqv).map g) :=
begin
  intros c₁ d₁ g iso_g, fapply is_iso.mk,
  { exact (concrete_full_hom_equiv c_eqv).map iso_g.inv },
  { rwr <- concrete_full_hom_equiv_comp, rwr iso_g.r_inv, 
    exact concrete_full_hom_equiv_id _ _ },
  { rwr <- concrete_full_hom_equiv_comp, rwr iso_g.l_inv, 
    exact concrete_full_hom_equiv_id _ _ }
end

@[hott]
def concrete_full_hom_equiv_inv {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} (c_eqv : concrete_equiv f₁ f₂) : Π {c₁ d₁ : C₁} (g : f₁ c₁ ≅ f₁ d₁),
  (concrete_full_hom_equiv c_eqv).map g.ih.inv = 
                                  is_iso.inv (concrete_full_hom_equiv_iso c_eqv g.ih) :=
λ c₁ d₁ g, idp

@[hott] 
def concrete_full_hom_funct {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} (c_eqv : concrete_equiv f₁ f₂) {c₁ c₁' d₁ d₁' : C₁} (pc : f₁ c₁ = f₁ c₁')
  (pd : f₁ d₁ = f₁ d₁') : Π (g : f₁ c₁ ⟶ f₁ d₁),
  (concrete_full_hom_equiv c_eqv).map ((idtoiso pc⁻¹).hom ≫ g ≫ (idtoiso pd).hom) =
    (idtoiso (c_eqv.comm_hom c₁')⁻¹).hom ≫ (idtoiso pc⁻¹).hom ≫ 
    (idtoiso (c_eqv.comm_hom c₁)).hom  ≫ ((concrete_full_hom_equiv c_eqv).map g) ≫ 
    (idtoiso (c_eqv.comm_hom d₁)⁻¹).hom ≫ (idtoiso pd).hom ≫ 
    (idtoiso (c_eqv.comm_hom d₁')).hom :=
begin
  intro g, rwr id_inv_iso_inv,
  change (idtoiso (c_eqv.comm_hom c₁')).ih.inv ≫ _ ≫ (idtoiso (c_eqv.comm_hom d₁')).hom =
            _ ≫ _ ≫ _ ≫ ((idtoiso (c_eqv.comm_hom c₁)).ih.inv ≫ g ≫ 
              (idtoiso (c_eqv.comm_hom d₁)).hom) ≫ _,
  rwr <- is_precat.assoc (idtoiso (c_eqv.comm_hom c₁)).hom,
  rwr <- is_precat.assoc (idtoiso (c_eqv.comm_hom c₁)).hom,
  rwr is_iso.l_inv, rwr is_precat.id_comp, 
  rwr is_precat.assoc g, rwr <- is_precat.assoc (idtoiso (c_eqv.comm_hom d₁)).hom, 
  rwr id_inv_iso_inv (c_eqv.comm_hom c₁'), rwr id_inv_iso_inv (c_eqv.comm_hom d₁), 
  change _ = (idtoiso (c_eqv.comm_hom c₁')).ih.inv ≫ (_ ≫ _ ≫ (_ ≫ (idtoiso (c_eqv.comm_hom d₁)).ih.inv) ≫ _),
  rwr is_iso.l_inv, rwr is_precat.id_comp,
  rwr is_precat.assoc _ (g ≫ _), rwr is_precat.assoc g
end

@[hott]
def concrete_equiv_hom_sys {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} [H₁ : concrete_hom_system f₁] (c_eqv : concrete_equiv f₂ f₁) :
  concrete_hom_system f₂ :=
begin
  fapply concrete_hom_system.mk,
  { intros c₂ d₂ g, 
    exact concrete_hom_system.hom f₁ _ _ ((concrete_full_hom_equiv c_eqv).map g) },
  { intro c₂, change ↥(concrete_hom_system.hom _ _ _ _), 
    rwr concrete_full_hom_equiv_id, exact concrete_hom_system.id _ _ },
  { intros c₂ d₂ e₂ g h g_el h_el, change ↥(concrete_hom_system.hom _ _ _ _),
    rwr concrete_full_hom_equiv_comp, exact concrete_hom_system.comp g_el h_el },
  { intros c₂ d₂ g iso_g g_el, 
    change ↥(concrete_hom_system.hom _ _ _ ((concrete_full_hom_equiv c_eqv).map 
                                                              (iso.mk g iso_g).ih.inv)),
    rwr concrete_full_hom_equiv_inv, exact concrete_hom_system.inv _ _ g_el }
end

@[hott]
def concrete_equiv_precat {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} [H₁ : concrete_hom_system f₁] (c_eqv : concrete_equiv f₂ f₁) :
  is_precat C₂ :=
@concrete_is_precat _ _ f₂ (concrete_equiv_hom_sys c_eqv)

@[hott]
def concrete_equiv_cat_struct {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} [H₁ : concrete_hom_system f₁] (c_eqv : concrete_equiv f₂ f₁) :
  category_struct C₂ := 
(concrete_equiv_precat c_eqv).to_category_struct

@[hott]
def concrete_equiv_hom {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} [H₁ : concrete_hom_system f₁] (c_eqv : concrete_equiv f₂ f₁) :
  has_hom C₂ := 
(concrete_equiv_precat c_eqv).to_has_hom

@[hott]
def concrete_equiv_hom_eqv {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} [H₁ : concrete_hom_system f₁] (c_eqv : concrete_equiv f₂ f₁) :
  Π {c₂ d₂ : C₂} (g : f₂ c₂ ⟶ f₂ d₂), 
    @concrete_hom_system.hom _ _ _ (concrete_equiv_hom_sys c_eqv) _ _ g <-> 
    concrete_hom_system.hom f₁ (c_eqv.eqv c₂) (c_eqv.eqv d₂) 
                                          ((concrete_full_hom_equiv c_eqv).map g) :=
λ c₂ d₂ g, pair (λ hom_g, hom_g) (λ hom_g, hom_g)

@[hott]
def concrete_equiv_hom_map {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} [H₁ : concrete_hom_system f₁] (c_eqv : concrete_equiv f₂ f₁) :
  Π (c₂ d₂ : C₂), (@has_hom.hom _ (concrete_equiv_hom c_eqv) c₂ d₂) -> 
                  (c_eqv.eqv c₂ ⟶ c_eqv.eqv d₂) :=
λ c₂ d₂, map_of_pred_Sets (concrete_full_hom_equiv c_eqv).map 
                          (λ g, (concrete_equiv_hom_eqv c_eqv g).1)

@[hott]
def concrete_equiv_hom_map_bij {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} [H₁ : concrete_hom_system f₁] (c_eqv : concrete_equiv f₂ f₁) :
  Π (c₂ d₂ : C₂), is_set_bijective (concrete_equiv_hom_map c_eqv c₂ d₂) :=
begin
  intros c₂ d₂, fapply bij_map_of_pred_Sets, exact (concrete_full_hom_equiv c_eqv).bij
end

@[hott]
def concrete_equiv_precat_iso {C₁ C₂ : Type _} {X : Category.{u' v}} {f₁ : C₁ -> X} 
  {f₂ : C₂ -> X} [H₁ : concrete_hom_system f₁] (c_eqv : concrete_equiv f₂ f₁) :
  @is_precat_iso C₂ C₁ (concrete_equiv_precat c_eqv) _ :=
begin
  fapply precat_iso.mk,
  { fapply precategories.functor.mk,
    { exact c_eqv.eqv },
    { exact concrete_equiv_hom_map c_eqv },
    { intro c₂, fapply sigma.sigma_eq,
      { exact concrete_full_hom_equiv_id c_eqv c₂ },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { intros c₂ d₂ e₂ g h, fapply sigma.sigma_eq,
      { exact concrete_full_hom_equiv_comp c_eqv g.1 h.1 },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } },
  { exact concrete_equiv_hom_map_bij c_eqv },
  { exact c_eqv.eqv.to_is_equiv }
end

/- We also show that the fibers of equivalent concrete categories are isomorphic as 
   precategories. -/

/- To minimize the proving obligations we introduce extensions of concrete categories. 
   
   The extra conditions that make a homomorphism of the underlying objects to a homomorphism of 
   the concrete type are collected in an `extra_hom_system`, satisfying the same properties
   than the conditions of a `concrete_hom_system`. The extension of the concrete category is then 
   obtained by intersecting these conditions with the conditions defining homomorphisms in the 
   concrete category. -/
@[hott]
class extra_hom_system {C D : Type u} {X : Category.{u' v}} (f : C -> D) (g : D -> X) :=
  (hom : Π c d : C, Subset (g (f c) ⟶ g (f d)))
  (id : ∀ c : C, 𝟙 (g (f c)) ∈ hom c c)
  (comp : ∀ {c d e : C} {h₁ : g (f c) ⟶ g (f d)} {h₂ : g (f d) ⟶ g (f e) }, 
            (h₁ ∈ hom c d) -> (h₂ ∈ hom d e) -> h₁ ≫ h₂ ∈ hom c e)
  (inv : ∀ {c d : C} (h : g (f c) ⟶ g (f d)) (hih : is_iso h), (h ∈ hom c d) -> 
                                                               (hih.inv ∈ hom d c))

@[hott, instance]
def extended_hom_system {C D : Type u} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] : concrete_hom_system (g ∘ f) :=
concrete_hom_system.mk 
  (λ c₁ c₂ : C, extra_hom_system.hom f g c₁ c₂ ∩ @concrete_hom_system.hom D _ g _ (f c₁) 
                                                                                   (f c₂)) 
  (λ c : C, (elem_inter_iff _ _ (𝟙 (g (f c)))).2 ⟨extra_hom_system.id f g c, 
                                                  @concrete_hom_system.id D _ g _ (f c)⟩) 
  (λ c d e h₁ h₂ h₁_el h₂_el, (elem_inter_iff _ _ (h₁ ≫ h₂)).2 
                            ⟨extra_hom_system.comp ((elem_inter_iff _ _ _).1 h₁_el).1 
                                                   ((elem_inter_iff _ _ _).1 h₂_el).1, 
                             concrete_hom_system.comp ((elem_inter_iff _ _ _).1 h₁_el).2 
                                                      ((elem_inter_iff _ _ _).1 h₂_el).2⟩) 
  (λ c d h hih h_el, (elem_inter_iff _ _ hih.inv).2 
                       ⟨extra_hom_system.inv h hih ((elem_inter_iff _ _ _).1 h_el).1, 
                        concrete_hom_system.inv h hih ((elem_inter_iff _ _ _).1 h_el).2⟩)

@[hott, instance]
def has_hom_fib_of_ext_hom_sys {C D : Type u} {X : Category.{u' v}} (f : C -> D) 
  (g : D -> X) [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] : 
  Π {x : X}, has_hom (fiber (g ∘ f) x) :=
@concrete_fib_has_hom _ _ (g ∘ f) (extended_hom_system f g)

@[hott, instance]
def cat_struct_rel_fib {C D : Type u} {X : Category.{u' v}} (f : C -> D) 
  (g : D -> X) [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] : 
  Π {x : X}, category_struct (fiber (g ∘ f) x) := by apply_instance

@[hott, instance]
def rel_fib_has_hom {C D : Type u} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] : 
  Π (d : D), has_hom (fiber f d) :=
λ x, has_hom.mk (λ c₁ c₂, to_Set (Σ (h : c₁.1 ⟶ c₂.1), (h.1 : g (f c₁.1) ⟶ g (f c₂.1)) = 
                                       (idtoiso (ap g c₁.2)).hom ≫ (idtoiso (ap g c₂.2⁻¹)).hom))

@[hott]
def rel_fib_hom_eq {C D : Type u} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] {d : D} {c₁ c₂ : fiber f d} : 
  Π {h₁ h₂ : c₁ ⟶ c₂}, (h₁.1.1 : g (f c₁.1) ⟶ g (f c₂.1)) = h₂.1.1 -> h₁ = h₂ :=
begin 
  intros h₁ h₂ hom_eq, fapply sigma.sigma_eq,
  { fapply sigma.sigma_eq, exact hom_eq, apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }  
end

@[hott, instance]
def rel_fib_cat_struct {C D : Type u} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] :
  Π (d : D), category_struct (fiber f d) :=
begin
  intro x, fapply category_struct.mk,
  { intro c, fapply dpair, exact 𝟙 c.1, 
    change 𝟙 (g (f c.1)) = _, rwr idtoiso_comp_eq, rwr <- ap_con, rwr con.right_inv },
  { intros a b c h₁ h₂, fapply dpair, exact h₁.1 ≫ h₂.1,
    have ph₁ : h₁.1.1 = _, from h₁.2,
    have ph₂ : h₂.1.1 = _, from h₂.2,
    change h₁.1.1 ≫ h₂.1.1 = _, rwr ph₁, rwr ph₂, 
    rwr is_precat.assoc (idtoiso (ap g a.point_eq)).hom, 
    rwr <-is_precat.assoc (idtoiso (ap g b.point_eq⁻¹)).hom,
    rwr idtoiso_comp_eq, rwr <- ap_con, rwr con.left_inv, 
    rwr ap_idp, rwr idtoiso_refl_eq, 
    change _ ≫ 𝟙 _ ≫ _ = _, rwr is_precat.id_comp }
end

@[hott, instance]
def rel_fib_is_precat {C D : Type u} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] :
  Π (d : D), is_precat (fiber f d) :=
begin
  intro d, fapply is_precat.mk,
  { intros c₁ c₂ h, fapply sigma.sigma_eq,
    { change 𝟙 c₁.1 ≫ h.1 = _, rwr @is_precat.id_comp _ _ c₁.1 c₂.1 h.1 },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { intros c₁ c₂ h, fapply sigma.sigma_eq,
    { change h.1 ≫ 𝟙 c₂.1 = _, rwr is_precat.comp_id },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { intros a b c d₁ h₁ h₂ i, fapply sigma.sigma_eq,
    { change (h₁.1 ≫ h₂.1) ≫ i.1 = h₁.1 ≫ h₂.1 ≫ i.1, 
      rwr @is_precat.assoc _ (concrete_is_precat (g ∘ f)) },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } 
end

@[hott]
class rel_fibs_are_cat {C D : Type u} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] :=
(homtoid : ∀ {d : D} {c₁ c₂ : fiber f d}, (c₁ ⟶ c₂) -> (c₁ = c₂))
(idhom_to_idp : ∀ {d : D} (c : fiber f d), homtoid (𝟙 c) = idp)

@[hott]
def rel_idhom_to_idp {C D : Type u} {X : Category.{u' v}} (f : C -> D) 
  (g : D -> X) [hs_g : concrete_hom_system g] [concrete_fibs_are_cat g] 
  [hs_f : extra_hom_system f g] [rfc : rel_fibs_are_cat f g] : 
  ∀ {d : D} (c : fiber f d) (h : c ⟶ c), h = 𝟙 c -> rel_fibs_are_cat.homtoid h = idp := 
begin intros d c h p, rwr p, exact rel_fibs_are_cat.idhom_to_idp g c end

@[hott]
def comp_fib_hom_to_fib_hom {C D : Type u} {X : Category.{u' v}} {f : C -> D}
  {g : D -> X} [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] {x : X} : 
  Π {c₁ c₂ : fiber (g ∘ f) x}, (c₁ ⟶ c₂) -> 
                             ((fiber.mk (f c₁.1) c₁.2) ⟶ (fiber.mk (f c₂.1) c₂.2)) :=
begin 
  intros c₁ c₂ h, fapply dpair, 
  { fapply dpair, exact h.1.1, exact ((elem_inter_iff _ _ _).1 h.1.2).2 },
  { exact h.2 }
end

@[hott]
def comp_fib_hom_to_rel_fib_hom {C D : Type u} {X : Category.{u' v}} {f : C -> D}
  {g : D -> X} [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] {x : X} : 
  Π {c₁ c₂ : fiber (g ∘ f) x} (p : f c₁.1 = f c₂.1) 
           (q : c₁.point_eq ⬝ c₂.point_eq⁻¹ = ap g p), (c₁ ⟶ c₂) -> 
                             (fiber.mk c₁.1 p ⟶ (fiber.mk c₂.1 idp)) :=
begin 
  intros c₁ c₂ p q h, fapply dpair,
  { fapply dpair, exact h.1.1, exact h.1.2 },
  { change h.1.1 = (idtoiso (ap g p)).hom ≫ (idtoiso (eq.inverse idp)).hom,
    have r : h.1.1 = _, from h.2, rwr r,  
    rwr idtoiso_comp_eq, rwr idtoiso_comp_eq, apply ap iso.hom, apply ap idtoiso,
    assumption }
end

@[hott]
def comp_fib_id_to_rel_fib_id {C D : Type u} {X : Category.{u' v}} {f : C -> D}
  {g : D -> X} [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] {x : X} : 
  Π (c : fiber (g ∘ f) x), 
  comp_fib_hom_to_rel_fib_hom idp (eq.con.right_inv c.point_eq) (𝟙 c) = 𝟙 (fiber_comp c).2 :=
begin intro c, apply rel_fib_hom_eq, exact idp end

@[hott, instance]
def rel_fib_cat_to_concrete_fibs_cat {C D : Type u} {X : Category.{u' v}} (f : C -> D) 
  (g : D -> X) [hs_g : concrete_hom_system g] [concrete_fibs_are_cat g] 
  [hs_f : extra_hom_system f g] [rfc : rel_fibs_are_cat f g] : 
  concrete_fibs_are_cat (g ∘ f) :=
begin
  fapply concrete_fibs_are_cat.mk, 
  { intros x c₁ c₂ h,
    apply λ p, (fib_comp_fib_eq c₁) ⬝ p ⬝ (fib_comp_fib_eq c₂)⁻¹, 
    fapply comp_fib_eq, 
    { apply concrete_fibs_are_cat.homtoid, exact comp_fib_hom_to_fib_hom h },
    { apply @ap _ _ fiber.point (@fiber.mk _ _ f (f c₂.1) c₁.1 (ap fiber.point 
                 (concrete_fibs_are_cat.homtoid (comp_fib_hom_to_fib_hom h)))) _, 
      apply @rel_fibs_are_cat.homtoid _ _ _ _ _ hs_g hs_f rfc, 
      fapply comp_fib_hom_to_rel_fib_hom, 
      exact eq.inverse (fiber_ap_ap _ _), exact h },
    { apply eq.concat (idp_con _), apply eq.inverse, apply eq.concat (con_idp _), 
      apply eq.concat (fiber_ap_ap f _), apply eq.concat (con_idp _), exact idp } },
  { intros x c, change fib_comp_fib_eq c ⬝ _ ⬝ (fib_comp_fib_eq c)⁻¹ = _, 
    apply con_inv_eq_of_eq_con, rwr idp_con (fib_comp_fib_eq c), 
    apply con_eq_of_eq_inv_con, rwr con.left_inv, 
    have r : (concrete_fibs_are_cat.homtoid (comp_fib_hom_to_fib_hom (𝟙 c))) = idp, from
      concrete_fibs_are_cat.idhom_to_idp _, rwr r, 
    have q : eq.inverse (fiber_ap_ap g idp) = 
                     con.right_inv (fiber.mk (f c.point) c.point_eq).point_eq, from 
        begin change eq.inverse (eq.inverse (con.right_inv _)) = _, rwr eq.inv_inv end,
    rwr q,
    have q₁ : rel_fibs_are_cat.homtoid (@comp_fib_hom_to_rel_fib_hom _ _ _ f g _ _ _ c c 
            (ap fiber.point (@idp _ (fiber.mk (f c.point) c.point_eq)))
            (con.right_inv (fiber.mk (f c.point) c.point_eq).point_eq) (𝟙 c)) = idp, from 
    begin
      apply rel_idhom_to_idp, 
      change (comp_fib_hom_to_rel_fib_hom idp (con.right_inv c.2) (𝟙 c)) = _,  
      rwr comp_fib_id_to_rel_fib_id c
    end, 
    rwr q₁, change comp_fib_eq f g idp idp _ = idp,
    apply comp_fib_eq_idp_idp, change idp ⬝ _ = eq.inverse idp, 
    apply eq.concat (idp_con _), apply ap eq.inverse, exact idp } 
end

/- If the concrete type is a family of dependent types with a homomorphism system we can
   deduce that the concrete type is a category from a condition on the dependent
   types. If the dependent types are the fibers, this is the same as the condition above
   showing that a general concrete type is a category. -/
@[hott]
class sigma_fibs_are_cat {X : Category.{u' v}} (B : X -> Type u)
  [concrete_hom_system (@sigma.fst X B)] :=
(homtoid : ∀ {x : X} {b₁ b₂ : B x} (g : dpair x b₁ ⟶ ⟨x,b₂⟩) (p : (g.1 : x ⟶ x) = 𝟙 x), 
                      b₁ = b₂)
(id_hom_to_idp : ∀ {x : X} {b : B x}, homtoid (𝟙 ⟨x,b⟩) idp = idp)

@[hott]
def sigma_fib_eq_to_concrete_fib_eq {A : Type _} {B : A -> Type _} {a : A} {b₁ b₂ : B a} :
  (b₁ = b₂) -> @fiber.mk (Σ (a : A), B a) A (@sigma.fst A B) a (dpair a b₁) idp = 
               fiber.mk (dpair a b₂) idp := 
begin intro p, hinduction p, fapply fiber.fiber_eq, exact idp, exact idp end 

@[hott]
def sigma_fib_idp_to_concrete_fib_idp {A : Type _} (B : A -> Type _) {a : A} {b : B a} :
  sigma_fib_eq_to_concrete_fib_eq (@idp _ b) = idp := idp

@[hott, hsimp]
def sigma_fib_isotoid {X : Category.{u' v}} {B : X -> Type u}
  [concrete_hom_system (@sigma.fst X B)] [sigma_fibs_are_cat B] : 
  Π {x : X} {c d : fiber (@sigma.fst X B) x}, (c ⟶ d) → c = d :=
begin
  intros x c d g, hinduction c with c c_eq, hinduction d with d d_eq,
  hinduction c with x₁ b₁, hinduction d with x₂ b₂, 
  hinduction c_eq, change x₂ = x₁ at d_eq, hinduction d_eq, 
  apply sigma_fib_eq_to_concrete_fib_eq, fapply sigma_fibs_are_cat.homtoid,
  exact g.1, have p : g.1.1 = _, from g.2, apply eq.concat p,
  apply eq.concat (idtoiso_comp_eq idp idp), exact ap iso.hom (idtoiso_refl_eq x₂)
end

@[hott]
def sigma_fib_idiso_to_idp {X : Category.{u' v}} {B : X -> Type u}
  [concrete_hom_system (@sigma.fst X B)] [sigma_fibs_are_cat B] : 
  Π {x : X} (c : fiber (@sigma.fst X B) x), sigma_fib_isotoid (𝟙 c) = idp :=
begin
  intros x₁ c, hinduction c with c c_eq, hinduction c with x b, change x = x₁ at c_eq,
  hinduction c_eq,  
  apply (λ p, p ⬝ sigma_fib_idp_to_concrete_fib_idp B),
  change sigma_fib_eq_to_concrete_fib_eq (sigma_fibs_are_cat.homtoid 
                                                                (𝟙 (dpair x b)) _) = _,
  apply ap sigma_fib_eq_to_concrete_fib_eq,
  apply (λ p, p ⬝ sigma_fibs_are_cat.id_hom_to_idp B),
  fapply apd011 sigma_fibs_are_cat.homtoid, exact idp,
  apply pathover_of_tr_eq, rwr idp_tr, hsimp 
end

@[hott, instance]
def concrete_sigma_fibs_are_cat {X : Category.{u' v}} (B : X -> Type u)
  [concrete_hom_system (@sigma.fst X B)] [sigma_fibs_are_cat B] : 
  concrete_fibs_are_cat (@sigma.fst X B) :=
begin
  fapply concrete_fibs_are_cat.mk,
  { exact λ x c d g, sigma_fib_isotoid g },
  { intros x c, exact sigma_fib_idiso_to_idp c } 
end

/- Now we use an equivalence of a general concrete type with a family of dependent types 
   to deduce that the concrete type is a category from the condition on the dependent 
   types. -/
@[hott]
class concrete_obj_system {C : Type u} {X : Category.{u' v}} (f : C -> X) 
  (fibs : X -> Type u'') := 
(fib_eqv : concrete_equiv f (@sigma.fst X fibs))

@[hott]
def concrete_eqv_sigma_fib {C : Type u} {X : Category.{u' v}} (f : C -> X) :
  C ≃ Σ (x : X), fiber f x :=
begin 
  fapply equiv.mk,
  { intro c, exact ⟨f c, ⟨c, idp⟩⟩ },
  { fapply adjointify,
    { intro fib, exact fib.2.1 },
    { intro b, hinduction b with x fib, hinduction fib with c c_eq,
      fapply sigma.sigma_eq, exact c_eq, hsimp, 
      fapply @apo _ _ _ _ _ _ c_eq _ _ (id : X -> X) (λ (x : X) (q : f c = x), fiber.mk c q), 
      apply pathover_of_tr_eq, hinduction c_eq, rwr idp_tr },
    { intro c, exact idp } }
end 

@[hott]
def concrete_map_obj_system {C : Type u} {X : Category.{u' v}} (f : C -> X) :
  concrete_obj_system f (λ x, fiber f x) :=
concrete_obj_system.mk (concrete_equiv.mk (concrete_eqv_sigma_fib f) (λ c, idp))

@[hott, instance]
def concrete_sigma_hom_system {C : Type u} {X : Category.{u' v}} (f : C -> X)
  (fibs : X -> Type u'') [H_obj : concrete_obj_system f fibs] 
  [H_hom : concrete_hom_system f] : concrete_hom_system (@sigma.fst X fibs) :=
concrete_equiv_hom_sys (concrete_equiv_inv H_obj.fib_eqv)

@[hott, instance]
def concrete_type_with_obj_sys_has_fib_cat {C : Type (u+1)} {X : Category.{u+1 v}} 
  (f : C -> X) (B : X -> Type u) [H_obj : concrete_obj_system f B] 
  [H_hom : concrete_hom_system f] [sigma_fibs_are_cat B] : concrete_fibs_are_cat f :=
begin
  fapply concrete_fibs_are_cat.mk,
  { intros x c d h, sorry },
  { sorry }
end

@[hott, instance]
def concrete_type_with_obj_sys_is_cat {C : Type (u+1)} {X : Category.{u+1 v}} (f : C -> X) 
  (B : X -> Type u) [H_obj : concrete_obj_system f B] [H_hom : concrete_hom_system f] 
  [sigma_fibs_are_cat B] : is_cat C :=
by apply_instance
  --fapply precat_iso_cat_cat (Σ (x : X), B x) C, 
  --{ exact concrete_equiv_precat_iso (concrete_equiv_inv 
  --                                   (concrete_obj_system.fib_eqv f (λ (x : ↥X), B x))) },
  --{ apply_instance }
--end

end hott