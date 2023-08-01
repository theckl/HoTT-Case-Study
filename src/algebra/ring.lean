import sets.basic categories.models

universes v v' u u' w 
hott_theory

namespace hott

open signature hott.set

namespace rings

/- At the moment, we only need commutative rings with one. -/

@[hott]
def ring_signature : fo_signature :=
begin
  fapply fo_signature.mk,
  exact nat_Set, -- let's see whether this is easier than introducing strings
  exact fin_Set 1, --one sort
  exact fin_Set 5, --five operations : add, mult, zero, one, neg
  exact fin_map_of_list [fin_Set 2, fin_Set 2, fin_Set 0, fin_Set 0, fin_Set 1], 
                                                            --arities of operations
  exact λ o a, ⟨0, nat.zero_lt_succ 0⟩, --sources and targets of operations can only                                     
  exact λ o, ⟨0, nat.zero_lt_succ 0⟩,   --have one sort
  exact fin_Set 0, --no extra relations : the laws for addition and multiplication are
                   --                     axioms of the theory of rings 
  intro f, hinduction nat.not_lt_zero f.1 f.2, --no arities of relations needed 
  exact λ r a, ⟨0, nat.zero_lt_succ 0⟩, --no sources of relations exist 
  exact fin_Set 0,  --no infinite dis-/conjunctions needed
  intro ind, hinduction nat.not_lt_zero ind.1 ind.2
end


end rings

end hott