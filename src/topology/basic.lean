import sets.setalgebra

universes u v w
hott_theory

namespace hott
open hott.set hott.subset 

set_option pp.universes true

/- A topology on the Set [T]. -/
variable T : Set.{u}

@[hott]
structure topological_space :=
(is_open        : Subset (𝒫 T))
(is_open_univ   : is_open (total_Subset T))
(is_open_inter  : ∀ U V : Subset T, is_open U → is_open V → is_open (U ∩ V)) 
(is_open_iUnion : ∀ (I : Set) (f : I -> 𝒫 T), (∀ i : I, is_open (f i)) -> 
                                                         is_open (⋃ᵢ f)) 
/- (is_open_sUnion : ∀ S : Subset (𝒫 T), (∀U, U ∈ S -> is_open U) → is_open (⋃₀ S)) 

    Since subsets are sets `is_open_iUnion` implies `is_open_sUnion`, but since the 
    map from `S` into `𝒫 T` is injective, `is_open_iUnion` is more general. 
    It is also more convenient when dealing with covers which are also defined
    as maps. -/ 

attribute [class] topological_space

@[hott]
def is_open [t : topological_space T] (U : Subset T): Prop :=
  topological_space.is_open t U

@[hott, hsimp]
def is_open_univ [t : topological_space T] : is_open T (total_Subset T) :=
  topological_space.is_open_univ t

@[hott]
def is_open_inter [t : topological_space T] {U V : Subset T} 
  (h₁ : is_open T U) (h₂ : is_open T V) : is_open T (U ∩ V) :=
topological_space.is_open_inter t U V h₁ h₂  

@[hott]
def is_open_iUnion [t : topological_space T] {I : Set} {f : I -> 𝒫 T}
  (h : ∀ i : I, is_open T (f i)) : is_open T (⋃ᵢ f) :=
topological_space.is_open_iUnion t I f h  

/- A constructor for topologies by specifying the closed sets, and showing 
   that they satisfy the appropriate conditions. -/
@[hott]   
def topological_space.of_closed 
  (is_closed : Subset T -> trunctype.{0} -1) 
  (is_closed_empty : is_closed (empty_Subset T)) 
  (is_closed_union : ∀ U V : Subset T, is_closed U → is_closed V → 
                                                     is_closed (U ∪ V)) 
  (is_closed_iInter : ∀ (I : Set) (f : I -> 𝒫 T), 
                        (∀ i : I, is_closed (f i)) -> is_closed (⋂ᵢ f)) : 
  topological_space T :=
begin
  fapply topological_space.mk, 
  { intro U, exact is_closed C(U) },
  { change (is_closed C(total_Subset T)).carrier, rwr compl_total_empty, 
    assumption },
  { intros U V cCU cCV, change (is_closed C(U ∩ V)).carrier, 
    rwr compl_inter U V, apply is_closed_union; assumption },
  { intros I f cCfi, change (is_closed C(⋃ᵢ f)).carrier, 
    rwr compl_iUnion, apply is_closed_iInter; assumption }
end    

end hott