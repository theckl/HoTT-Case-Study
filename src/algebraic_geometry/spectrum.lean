import rings.modules

universes u u' v w
hott_theory

set_option old_structure_cmd true

namespace hott

open hott.algebra hott.subset hott.trunc

namespace algebraic_geometry

end algebraic_geometry

@[hott]
def prime_spectrum (R : CommRing) := PrimeIdeal_Set R

@[hott]
def zero_locus_pred (R : CommRing) : 
  Ideal_Set R -> Setpred (prime_spectrum R) :=
λ I P, prop_ulift (I.carrier ⊆ P.1.carrier)

@[hott]
def is_Zariski_closed {R : CommRing} : Subset (prime_spectrum R) -> Prop :=
  λ Z, image (zero_locus_pred R) (sset_to_pred Z)

@[hott]
def empty_Zariski_closed (R : CommRing) : 
  is_Zariski_closed (empty_Subset (prime_spectrum R)) :=
begin 
  apply tr, sorry
end      

end hott