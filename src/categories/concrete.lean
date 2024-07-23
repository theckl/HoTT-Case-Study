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
class concrete_hom_system {C : Type u} {X : Category} (f : C -> X) :=
  (hom : Π c d : C, Subset (f c ⟶ f d))
  (id : ∀ c : C, 𝟙 (f c) ∈ hom c c)
  (comp : ∀ {c d e : C} {g : f c ⟶ f d} {h : f d ⟶ f e}, 
            (g ∈ hom c d) -> (h ∈ hom d e) -> g ≫ h ∈ hom c e)

@[hott, instance]
def concrete_has_hom {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : has_hom C :=
has_hom.mk (λ c d : C, pred_Set (concrete_hom_system.hom f c d)) 

@[hott, instance, hsimp]
def concrete_cat_struct {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : category_struct C :=
category_struct.mk
  (λ a, ⟨𝟙 (f a), concrete_hom_system.id f a⟩)
  (λ c d e g h, ⟨g.1 ≫ h.1, concrete_hom_system.comp g.2 h.2⟩)

@[hott, instance, hsimp]
def concrete_is_precat {C : Type u} {X : Category} (f : C -> X) 
  [hom_sys : concrete_hom_system f] : is_precat C :=
begin
  fapply is_precat.mk,
    intros a b g, apply pred_Set_eq, hsimp,
    intros a b g, apply pred_Set_eq, hsimp,
    intros, apply pred_Set_eq, hsimp
end 

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
    sorry }
end

end hott