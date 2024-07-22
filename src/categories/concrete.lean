import sets.subset categories.basic

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc 
     hott.is_equiv hott.precategories hott.categories

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

end hott
