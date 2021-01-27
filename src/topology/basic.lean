import setalgebra

universes u v w
hott_theory

namespace hott
open hott.set hott.subset 

/- A topology on the Set [T]. -/
variable T : Set.{u}

@[hott]
structure topological_space :=
(is_open        : Subset T → trunctype.{u} -1)
(is_open_univ   : is_open (total_Subset T))
(is_open_inter  : ∀ U V : Subset T, is_open U → is_open V → is_open (U ∩ V)) 
(is_open_sUnion : ∀ S : Subset (𝒫 T), (∀U, U ∈ S -> is_open U) → is_open (⋃₀ S)) 

attribute [class] topological_space

end hott