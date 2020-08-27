import hott.init

universes u v w
hott_theory

namespace hott
open is_trunc

namespace set

/- We need the empty set, the identity map between sets and some properties of maps between sets. They can be 
   derived from properties of general (n-)types, in [function], but we give them separate definitions adapted 
   to sets, to make them more accessible. -/

@[hott]
def empty_Set : Set := 
  Set.mk empty (is_trunc_succ empty -1)

@[hott]
def id_map (A : Set) : A -> A :=
  (id : A -> A)    

@[hott]
lemma id_map_is_right_neutral {A B : Set} (map : A -> B) :
  map ∘ (id_map A) = map :=
begin
  simp,
  
end      

end set

end hott
