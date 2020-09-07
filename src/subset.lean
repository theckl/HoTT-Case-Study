import hott.init set_theory

universes u v w
hott_theory

namespace hott

namespace subset
open set

/- We define subsets of sets [A] as a set [B] together with an injective map [i: B -> A],
   implemented as a bundled structure.  -/

@[hott]
structure Subset (A : Set) :=
   (carrier : Set) (map : carrier -> A) (inj : set.is_set_injective map)

end subset

end hott