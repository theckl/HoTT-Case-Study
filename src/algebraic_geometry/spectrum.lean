import rings.modules

universes u u' v w
hott_theory

set_option old_structure_cmd true

namespace hott

open hott.algebra hott.subset 

namespace algebraic_geometry

end algebraic_geometry

@[hott]
def prime_spectrum (R : CommRing) := PrimeIdeal_Set R

@[hott]
def zero_locus_pred (R : CommRing) : 
  Ideal_Set R -> Setpred (prime_spectrum R) :=
λ I P, prop_ulift (I.carrier ⊆ P.1.carrier)

end hott