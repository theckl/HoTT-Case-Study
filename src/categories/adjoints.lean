import categories.examples

universes v v' u u' w
hott_theory

namespace hott
open hott.categories

namespace categories.adjoints

@[hott]
structure adjunction (C : Type u) (D : Type u') [precategory.{v} C] 
  [precategory.{v'} D] :=
(L : functor C D)
(R : functor D C)
(adj : id_functor C ⟹ L ⋙ R)
(adj_hom : Π {c : C} {d : D} (f : c ⟶ R.obj d), 
                                    Σ (g : L.obj c ⟶ d), f = adj.app c ≫ R.map g)
(adj_uniq : Π {c : C} {d : D} (f : c ⟶ R.obj d) (g : L.obj c ⟶ d), 
                                    f = adj.app c ≫ R.map g -> g = (adj_hom f).1)                                      

end categories.adjoints

end hott