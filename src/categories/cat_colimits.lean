import setalgebra categories.examples

universes v u v' u' w
hott_theory

namespace hott
open hott.eq hott.is_trunc hott.trunc hott.set hott.subset 
     hott.categories 

/- We introduce colimits of diagrams mapped to categories, by using cocones to 
   pick the universal object and encode the universal property.

   As far as possible we copy the mathlib-code in [category_theory.limits]. -/

namespace category_theory.colimits

structure cocone {J : Set.{v}} [precategory J] {C : Type u} 
  [precategory C] (F : J ⥤ C) :=
(X : C)
(π : F ⟹ (constant_functor J C X))

end category_theory.colimits

end hott