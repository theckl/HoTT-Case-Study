import setalgebra category_theory

universes v u v' u' w
hott_theory

namespace hott
open hott.set hott.subset hott.category_theory

/- We introduce limits of diagrams mapped to categories, by using cones to 
   pick the universal object and encode the universal property.

   As far as possible we copy the mathlib-code in [category_theory.limits]. -/

namespace category_theory.limits

structure cone {J : Set.{v}} [precategory J] {C : Type u} 
  [precategory C] (F : J ⥤ C) :=
(c : C)
(π : (constant_functor J C c) ⟹ F)

end category_theory.limits

end hott