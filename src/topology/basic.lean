import setalgebra

universes u v w
hott_theory

namespace hott
open hott.set hott.subset 

set_option pp.universes true

/-
#print instances has_inter
#print subset_inter

#print sUnion 
-/
/- A topology on the Set [T]. -/
variable T : Set

@[hott]
structure topological_space :=
(is_open        : Subset T → Prop)
(is_open_univ   : is_open (total_Subset T))
/-
(is_open_inter  : ∀U V : Subset T, is_open U → is_open V → /- is_open (U ∩ V)) -/
                                   is_open (@has_inter.inter (Subset T) (subset_inter) U V))
-/
(is_open_sUnion : ∀S : Subset (𝒫 T), (∀U, U ∈ S -> is_open U) → /- is_open (⋃₀ S)) -/
                      is_open ({t ∈ T | @exists_elem _ (λ (B : 𝒫 T), B ∈ S and t ∈ B)})) 

#check T

/-
@[hott]
def test_inter (A : Set) : Subset A -> Subset A -> Subset A :=
  assume B C, B ∩ C     

@[hott]
def test_inter2 (A : Type _) : set A -> set A -> set A :=
  assume B C, B ∩ C 

attribute [class] topological_space
-/
end hott