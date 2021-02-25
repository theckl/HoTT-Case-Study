import setalgebra category_theory

universes v u v' u' w
hott_theory

namespace hott
open hott.trunc hott.set hott.subset hott.category_theory

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

end category_theory.limits

end hott