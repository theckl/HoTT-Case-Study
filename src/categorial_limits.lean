import setalgebra category_theory

universes v u v' u' w
hott_theory

namespace hott
open hott.is_trunc hott.trunc hott.set hott.subset hott.category_theory

/- We introduce limits of diagrams mapped to categories, by using cones to 
   pick the universal object and encode the universal property.

   As far as possible we copy the mathlib-code in [category_theory.limits]. -/

namespace category_theory.limits

structure cone {J : Set.{v}} [precategory J] {C : Type u} 
  [precategory C] (F : J ⥤ C) :=
(X : C)
(π : (constant_functor J C X) ⟹ F)

@[hott]
structure is_limit {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} (t : cone F) :=
(lift : Π (s : cone F), s.X ⟶ t.X)
(fac  : ∀ (s : cone F) (j : J), lift s ≫ t.π.app j = s.π.app j)
(uniq : ∀ (s : cone F) (m : s.X ⟶ t.X) 
          (w : ∀ j : J, m ≫ t.π.app j = s.π.app j), m = lift s)

@[hott]
def limit_cone_point_iso {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} (s t : cone F) [is_limit s] [is_limit t] : s.X ≅ t.X :=
sorry  

/- `limit_cone F` contains a cone over `F` together with the information that 
   it is a limit. -/
@[hott]
structure limit_cone {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

/- `has_limit F` represents the mere existence of a limit for `F`. This allows
   to define as a class with instances. However, if `C` is a category, 
   `limit_cone F` is a (-1)-Type since limits are determined up to isomorphism,
   so we can extract a limit cone from `has_limit`. -/
@[hott]   
class has_limit {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  (F : J ⥤ C) :=
mk' :: (exists_limit : ∥limit_cone F∥)

@[hott]
def has_limit.mk {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} (d : limit_cone F) :=
has_limit.mk' (tr d)  

@[hott]
def limit_cone_is_unique {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) : ∀ lc₁ lc₂ : limit_cone F, lc₁ = lc₂ :=
assume lc₁ lc₂,
have lc_eta : ∀ lc : limit_cone F, lc = ⟨lc.cone, lc.is_limit⟩, by
  intro lc; hinduction lc; refl,
have cone_id : lc₁.cone = lc₂.cone, from sorry,
have is_limit_id : lc₁.is_limit =[cone_id] lc₂.is_limit, from sorry,  
calc lc₁ = ⟨lc₁.cone, lc₁.is_limit⟩ : lc_eta lc₁
     ... = ⟨lc₂.cone, lc₂.is_limit⟩ : apd011 _ cone_id is_limit_id
     ... = lc₂ : (lc_eta lc₂)⁻¹  

@[hott, instance]
def limit_cone_is_prop {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) : is_trunc -1 (limit_cone F) :=
is_prop.mk (limit_cone_is_unique F)

@[hott]
def get_limit_cone {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) [has_limit F] : limit_cone F :=
untrunc_of_is_trunc (has_limit.exists_limit F)  

end category_theory.limits

end hott