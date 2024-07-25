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

@[hott, instance]
def concrete_has_hom {C : Type u} {X : Category.{u u}} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : has_hom C :=
has_hom.mk (λ c d : C, pred_Set (concrete_hom_system.hom f c d)) 

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
sorry

@[hott, instance]
def concrete_fib_has_hom {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : Π (x : X), has_hom (fiber f x) :=
λ x, has_hom.mk (λ c d, to_Set (Σ (h : c.1 ⟶ d.1), 
                    (idtoiso c.2⁻¹).hom ≫ h.1 ≫ (idtoiso d.2).hom = 𝟙 x))

@[hott, instance]
def concrete_fib_cat_struct {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : Π (x : X), category_struct (fiber f x) :=
begin
  intro x, fapply category_struct.mk,
  { intro c, fapply dpair, exact 𝟙 c.1, 
    change _ ≫ 𝟙 (f c.1) ≫ _ = _, rwr is_precat.id_comp, rwr idtoiso_comp_eq,
    rwr con.left_inv },
  { intros a b c g h, fapply dpair, exact g.1 ≫ h.1,
    change _ ≫ (g.1.1 ≫ h.1.1) ≫ _ = _, rwr <- is_precat.id_comp h.1.1, 
    rwr <- is_iso.l_inv (idtoiso b.point_eq).ih, rwr <- is_precat.assoc g.1.1,
    rwr <- is_precat.assoc g.1.1, rwr is_precat.assoc _ _ h.1.1, 
    rwr is_precat.assoc _ _ (idtoiso c.point_eq).hom, 
    rwr is_precat.assoc _ _ (idtoiso c.point_eq).hom,
    rwr <- is_precat.assoc (idtoiso (a.point_eq)⁻¹).hom,
    hinduction g with g g_eq, rwr g_eq, 
    change _ ≫ (inv_iso _).hom ≫ _ ≫ _ = _, 
    rwr <- id_inv_iso_inv, hinduction h with h h_eq, rwr h_eq, 
    rwr is_precat.id_comp }
end

--set_option trace.class_instances true

@[hott, instance]
def concrete_fib_is_precat {C : Type u} {X : Category.{u u}} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : Π (x : X), is_precat (fiber f x) :=
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

--set_option trace.class_instances false

@[hott]
def concrete_fib_cat_iso_to_id {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] (is_cat_fibs : Π (x : X), is_cat (fiber f x)) :
  Π (c d : C), (c ≅ d) -> (c = d) :=
begin
  intros c d i, sorry
end 

@[hott, instance]
def concrete_fib_cat_to_concrete_cat {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : (Π (x : X), is_cat (fiber f x)) -> 
  is_cat C :=
begin
  intro is_cat_fibs,
  apply is_cat.mk , intros c d, fapply adjointify,
  { exact concrete_fib_cat_iso_to_id f is_cat_fibs c d },
  { sorry },
  { sorry }
end

end hott